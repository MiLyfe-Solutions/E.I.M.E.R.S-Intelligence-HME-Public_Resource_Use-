import V185TrunkScan23Chunk0700

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4144587 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_4144587 : Nat := 118140960795 + 4144587 * 2 ^ 59
def prefixEnd_4144587 : Nat := 4983230072969 + 3 ^ 40 * 4144587 * 2
def baseEnd_4144587 : Nat := 2128165245376081018001897

theorem tailTrace_4144587 : CollatzResearch.WordTrace tailWord_4144587 prefixEnd_4144587 2128165245376081018001897 := by
  unfold tailWord_4144587
  simp only [CollatzResearch.WordTrace]
  refine ⟨151165506635876612950760015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100777004423917741967173343 151165506635876612950760015)
  ·
    refine ⟨226748259953814919426140023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151165506635876612950760015 226748259953814919426140023)
    ·
      refine ⟨340122389930722379139210035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226748259953814919426140023 340122389930722379139210035)
      ·
        refine ⟨510183584896083568708815053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340122389930722379139210035 510183584896083568708815053)
        ·
          refine ⟨191318844336031338265805645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510183584896083568708815053 191318844336031338265805645)
          ·
            refine ⟨71744566626011751849677117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191318844336031338265805645 71744566626011751849677117)
            ·
              refine ⟨26904212484754406943628919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71744566626011751849677117 26904212484754406943628919)
              ·
                refine ⟨40356318727131610415443379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26904212484754406943628919 40356318727131610415443379)
                ·
                  refine ⟨60534478090697415623165069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40356318727131610415443379 60534478090697415623165069)
                  ·
                    refine ⟨22700429284011530858686901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60534478090697415623165069 22700429284011530858686901)
                    ·
                      refine ⟨2128165245376081018001897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22700429284011530858686901 2128165245376081018001897)
                      ·
                        rfl

theorem cell23_4144587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_4144587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144587 prefixEnd_4144587 := by exact prefixLift 4144587
  have htrace : WordTrace (prefixWord ++ tailWord_4144587) baseStart_4144587 baseEnd_4144587 := by
    simpa [prefixWord, tailWord_4144587, baseEnd_4144587] using wordTrace_append hprefix tailTrace_4144587
  have hstable : (prefixWord ++ tailWord_4144587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144587).length < 2 ^ (prefixWord ++ tailWord_4144587).sum := by decide
  have hdescent : baseEnd_4144587 < baseStart_4144587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144588 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4144588 : Nat := 118140960795 + 4144588 * 2 ^ 59
def prefixEnd_4144588 : Nat := 4983230072969 + 3 ^ 40 * 4144588 * 2
def baseEnd_4144588 : Nat := 2128165758856735514089393

theorem tailTrace_4144588 : CollatzResearch.WordTrace tailWord_4144588 prefixEnd_4144588 2128165758856735514089393 := by
  unfold tailWord_4144588
  simp only [CollatzResearch.WordTrace]
  refine ⟨75582771554436495060773209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100777028739248660081030945 75582771554436495060773209)
  ·
    refine ⟨56687078665827371295579907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75582771554436495060773209 56687078665827371295579907)
    ·
      refine ⟨85030617998741056943369861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56687078665827371295579907 85030617998741056943369861)
      ·
        refine ⟨15943240874763948176881849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85030617998741056943369861 15943240874763948176881849)
        ·
          refine ⟨11957430656072961132661387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15943240874763948176881849 11957430656072961132661387)
          ·
            refine ⟨17936145984109441698992081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957430656072961132661387 17936145984109441698992081)
            ·
              refine ⟨13452109488082081274244061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17936145984109441698992081 13452109488082081274244061)
              ·
                refine ⟨5044541058030780477841523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13452109488082081274244061 5044541058030780477841523)
                ·
                  refine ⟨7566811587046170716762285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044541058030780477841523 7566811587046170716762285)
                  ·
                    refine ⟨2837554345142314018785857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7566811587046170716762285 2837554345142314018785857)
                    ·
                      refine ⟨2128165758856735514089393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2837554345142314018785857 2128165758856735514089393)
                      ·
                        rfl

theorem cell23_4144588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4144588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144588 prefixEnd_4144588 := by exact prefixLift 4144588
  have htrace : WordTrace (prefixWord ++ tailWord_4144588) baseStart_4144588 baseEnd_4144588 := by
    simpa [prefixWord, tailWord_4144588, baseEnd_4144588] using wordTrace_append hprefix tailTrace_4144588
  have hstable : (prefixWord ++ tailWord_4144588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144588).length < 2 ^ (prefixWord ++ tailWord_4144588).sum := by decide
  have hdescent : baseEnd_4144588 < baseStart_4144588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144661 : List Nat := [1, 3, 2, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_4144661 : Nat := 118140960795 + 4144661 * 2 ^ 59
def prefixEnd_4144661 : Nat := 4983230072969 + 3 ^ 40 * 4144661 * 2
def baseEnd_4144661 : Nat := 2128203242944513728476557

theorem tailTrace_4144661 : CollatzResearch.WordTrace tailWord_4144661 prefixEnd_4144661 2128203242944513728476557 := by
  unfold tailWord_4144661
  simp only [CollatzResearch.WordTrace]
  refine ⟨151168205637608523588953837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100778803758405682392635891 151168205637608523588953837)
  ·
    refine ⟨56688077114103196345857689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151168205637608523588953837 56688077114103196345857689)
    ·
      refine ⟨42516057835577397259393267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56688077114103196345857689 42516057835577397259393267)
      ·
        refine ⟨63774086753366095889089901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42516057835577397259393267 63774086753366095889089901)
        ·
          refine ⟨23915282532512285958408713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63774086753366095889089901 23915282532512285958408713)
          ·
            refine ⟨17936461899384214468806535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23915282532512285958408713 17936461899384214468806535)
            ·
              refine ⟨26904692849076321703209803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17936461899384214468806535 26904692849076321703209803)
              ·
                refine ⟨40357039273614482554814705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26904692849076321703209803 40357039273614482554814705)
                ·
                  refine ⟨30267779455210861916111029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40357039273614482554814705 30267779455210861916111029)
                  ·
                    refine ⟨2837604323926018304635409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30267779455210861916111029 2837604323926018304635409)
                    ·
                      refine ⟨2128203242944513728476557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2837604323926018304635409 2128203242944513728476557)
                      ·
                        rfl

theorem cell23_4144661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_4144661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144661 prefixEnd_4144661 := by exact prefixLift 4144661
  have htrace : WordTrace (prefixWord ++ tailWord_4144661) baseStart_4144661 baseEnd_4144661 := by
    simpa [prefixWord, tailWord_4144661, baseEnd_4144661] using wordTrace_append hprefix tailTrace_4144661
  have hstable : (prefixWord ++ tailWord_4144661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144661).length < 2 ^ (prefixWord ++ tailWord_4144661).sum := by decide
  have hdescent : baseEnd_4144661 < baseStart_4144661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144691 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 4]
def baseStart_4144691 : Nat := 118140960795 + 4144691 * 2 ^ 59
def prefixEnd_4144691 : Nat := 4983230072969 + 3 ^ 40 * 4144691 * 2
def baseEnd_4144691 : Nat := 2128218647364148611101419

theorem tailTrace_4144691 : CollatzResearch.WordTrace tailWord_4144691 prefixEnd_4144691 2128218647364148611101419 := by
  unfold tailWord_4144691
  simp only [CollatzResearch.WordTrace]
  refine ⟨151169299827499838712545927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100779533218333225808363951 151169299827499838712545927)
  ·
    refine ⟨226753949741249758068818891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151169299827499838712545927 226753949741249758068818891)
    ·
      refine ⟨340130924611874637103228337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226753949741249758068818891 340130924611874637103228337)
      ·
        refine ⟨255098193458905977827421253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340130924611874637103228337 255098193458905977827421253)
        ·
          refine ⟨47830911273544870842641485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255098193458905977827421253 47830911273544870842641485)
          ·
            refine ⟨17936591727579326565990557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47830911273544870842641485 17936591727579326565990557)
            ·
              refine ⟨6726221897842247462246459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17936591727579326565990557 6726221897842247462246459)
              ·
                refine ⟨10089332846763371193369689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726221897842247462246459 10089332846763371193369689)
                ·
                  refine ⟨7566999635072528395027267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089332846763371193369689 7566999635072528395027267)
                  ·
                    refine ⟨11350499452608792592540901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7566999635072528395027267 11350499452608792592540901)
                    ·
                      refine ⟨2128218647364148611101419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11350499452608792592540901 2128218647364148611101419)
                      ·
                        rfl

theorem cell23_4144691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 4].length) (baseStart_4144691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144691 prefixEnd_4144691 := by exact prefixLift 4144691
  have htrace : WordTrace (prefixWord ++ tailWord_4144691) baseStart_4144691 baseEnd_4144691 := by
    simpa [prefixWord, tailWord_4144691, baseEnd_4144691] using wordTrace_append hprefix tailTrace_4144691
  have hstable : (prefixWord ++ tailWord_4144691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144691).length < 2 ^ (prefixWord ++ tailWord_4144691).sum := by decide
  have hdescent : baseEnd_4144691 < baseStart_4144691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144714 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_4144714 : Nat := 118140960795 + 4144714 * 2 ^ 59
def prefixEnd_4144714 : Nat := 4983230072969 + 3 ^ 40 * 4144714 * 2
def baseEnd_4144714 : Nat := 236470050824355780123757

theorem tailTrace_4144714 : CollatzResearch.WordTrace tailWord_4144714 prefixEnd_4144714 236470050824355780123757 := by
  unfold tailWord_4144714
  simp only [CollatzResearch.WordTrace]
  refine ⟨37792534676604128410158299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100780092470944342427088797 37792534676604128410158299)
  ·
    refine ⟨56688802014906192615237449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37792534676604128410158299 56688802014906192615237449)
    ·
      refine ⟨42516601511179644461428087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56688802014906192615237449 42516601511179644461428087)
      ·
        refine ⟨63774902266769466692142131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42516601511179644461428087 63774902266769466692142131)
        ·
          refine ⟨95662353400154200038213197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63774902266769466692142131 95662353400154200038213197)
          ·
            refine ⟨35873382525057825014329949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95662353400154200038213197 35873382525057825014329949)
            ·
              refine ⟨13452518446896684380373731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35873382525057825014329949 13452518446896684380373731)
              ·
                refine ⟨20178777670345026570560597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13452518446896684380373731 20178777670345026570560597)
                ·
                  refine ⟨236470050824355780123757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20178777670345026570560597 236470050824355780123757)
                  ·
                    rfl

theorem cell23_4144714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_4144714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144714 prefixEnd_4144714 := by exact prefixLift 4144714
  have htrace : WordTrace (prefixWord ++ tailWord_4144714) baseStart_4144714 baseEnd_4144714 := by
    simpa [prefixWord, tailWord_4144714, baseEnd_4144714] using wordTrace_append hprefix tailTrace_4144714
  have hstable : (prefixWord ++ tailWord_4144714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144714).length < 2 ^ (prefixWord ++ tailWord_4144714).sum := by decide
  have hdescent : baseEnd_4144714 < baseStart_4144714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144761 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 1, 5]
def baseStart_4144761 : Nat := 118140960795 + 4144761 * 2 ^ 59
def prefixEnd_4144761 : Nat := 4983230072969 + 3 ^ 40 * 4144761 * 2
def baseEnd_4144761 : Nat := 709418197003321112408699

theorem tailTrace_4144761 : CollatzResearch.WordTrace tailWord_4144761 prefixEnd_4144761 709418197003321112408699 := by
  unfold tailWord_4144761
  simp only [CollatzResearch.WordTrace]
  refine ⟨151171852937246240667594137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100781235291497493778396091 151171852937246240667594137)
  ·
    refine ⟨113378889702934680500695603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151171852937246240667594137 113378889702934680500695603)
    ·
      refine ⟨170068334554402020751043405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113378889702934680500695603 170068334554402020751043405)
      ·
        refine ⟨63775625457900757781641277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170068334554402020751043405 63775625457900757781641277)
        ·
          refine ⟨23915859546712784168115479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63775625457900757781641277 23915859546712784168115479)
          ·
            refine ⟨35873789320069176252173219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23915859546712784168115479 35873789320069176252173219)
            ·
              refine ⟨53810683980103764378259829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35873789320069176252173219 53810683980103764378259829)
              ·
                refine ⟨5044751623134727910461859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53810683980103764378259829 5044751623134727910461859)
                ·
                  refine ⟨7567127434702091865692789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044751623134727910461859 7567127434702091865692789)
                  ·
                    refine ⟨709418197003321112408699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7567127434702091865692789 709418197003321112408699)
                    ·
                      rfl

theorem cell23_4144761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_4144761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144761 prefixEnd_4144761 := by exact prefixLift 4144761
  have htrace : WordTrace (prefixWord ++ tailWord_4144761) baseStart_4144761 baseEnd_4144761 := by
    simpa [prefixWord, tailWord_4144761, baseEnd_4144761] using wordTrace_append hprefix tailTrace_4144761
  have hstable : (prefixWord ++ tailWord_4144761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144761).length < 2 ^ (prefixWord ++ tailWord_4144761).sum := by decide
  have hdescent : baseEnd_4144761 < baseStart_4144761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144768 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 2, 3, 2]
def baseStart_4144768 : Nat := 118140960795 + 4144768 * 2 ^ 59
def prefixEnd_4144768 : Nat := 4983230072969 + 3 ^ 40 * 4144768 * 2
def baseEnd_4144768 : Nat := 2128258185374544809838565

theorem tailTrace_4144768 : CollatzResearch.WordTrace tailWord_4144768 prefixEnd_4144768 2128258185374544809838565 := by
  unfold tailWord_4144768
  simp only [CollatzResearch.WordTrace]
  refine ⟨75586054124110440431549479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100781405498813920575399305 75586054124110440431549479)
  ·
    refine ⟨113379081186165660647324219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75586054124110440431549479 113379081186165660647324219)
    ·
      refine ⟨170068621779248490970986329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113379081186165660647324219 170068621779248490970986329)
      ·
        refine ⟨127551466334436368228239747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170068621779248490970986329 127551466334436368228239747)
        ·
          refine ⟨191327199501654552342359621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127551466334436368228239747 191327199501654552342359621)
          ·
            refine ⟨35873849906560228564192429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191327199501654552342359621 35873849906560228564192429)
            ·
              refine ⟨13452693714960085711572161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35873849906560228564192429 13452693714960085711572161)
              ·
                refine ⟨10089520286220064283679121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13452693714960085711572161 10089520286220064283679121)
                ·
                  refine ⟨7567140214665048212759341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089520286220064283679121 7567140214665048212759341)
                  ·
                    refine ⟨2837677580499393079784753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7567140214665048212759341 2837677580499393079784753)
                    ·
                      refine ⟨2128258185374544809838565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2837677580499393079784753 2128258185374544809838565)
                      ·
                        rfl

theorem cell23_4144768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_4144768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144768 prefixEnd_4144768 := by exact prefixLift 4144768
  have htrace : WordTrace (prefixWord ++ tailWord_4144768) baseStart_4144768 baseEnd_4144768 := by
    simpa [prefixWord, tailWord_4144768, baseEnd_4144768] using wordTrace_append hprefix tailTrace_4144768
  have hstable : (prefixWord ++ tailWord_4144768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144768).length < 2 ^ (prefixWord ++ tailWord_4144768).sum := by decide
  have hdescent : baseEnd_4144768 < baseStart_4144768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144775 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_4144775 : Nat := 118140960795 + 4144775 * 2 ^ 59
def prefixEnd_4144775 : Nat := 4983230072969 + 3 ^ 40 * 4144775 * 2
def baseEnd_4144775 : Nat := 2128261779739126282451033

theorem tailTrace_4144775 : CollatzResearch.WordTrace tailWord_4144775 prefixEnd_4144775 2128261779739126282451033 := by
  unfold tailWord_4144775
  simp only [CollatzResearch.WordTrace]
  refine ⟨151172363559195521058603779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100781575706130347372402519 151172363559195521058603779)
  ·
    refine ⟨226758545338793281587905669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151172363559195521058603779 226758545338793281587905669)
    ·
      refine ⟨42517227251023740297732313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226758545338793281587905669 42517227251023740297732313)
      ·
        refine ⟨31887920438267805223299235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42517227251023740297732313 31887920438267805223299235)
        ·
          refine ⟨47831880657401707834948853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31887920438267805223299235 47831880657401707834948853)
          ·
            refine ⟨4484238811631410109526455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47831880657401707834948853 4484238811631410109526455)
            ·
              refine ⟨6726358217447115164289683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484238811631410109526455 6726358217447115164289683)
              ·
                refine ⟨10089537326170672746434525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726358217447115164289683 10089537326170672746434525)
                ·
                  refine ⟨3783576497314002279912947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10089537326170672746434525 3783576497314002279912947)
                  ·
                    refine ⟨5675364745971003419869421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3783576497314002279912947 5675364745971003419869421)
                    ·
                      refine ⟨2128261779739126282451033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675364745971003419869421 2128261779739126282451033)
                      ·
                        rfl

theorem cell23_4144775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_4144775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144775 prefixEnd_4144775 := by exact prefixLift 4144775
  have htrace : WordTrace (prefixWord ++ tailWord_4144775) baseStart_4144775 baseEnd_4144775 := by
    simpa [prefixWord, tailWord_4144775, baseEnd_4144775] using wordTrace_append hprefix tailTrace_4144775
  have hstable : (prefixWord ++ tailWord_4144775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144775).length < 2 ^ (prefixWord ++ tailWord_4144775).sum := by decide
  have hdescent : baseEnd_4144775 < baseStart_4144775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144818 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3]
def baseStart_4144818 : Nat := 118140960795 + 4144818 * 2 ^ 59
def prefixEnd_4144818 : Nat := 4983230072969 + 3 ^ 40 * 4144818 * 2
def baseEnd_4144818 : Nat := 2128283859407269614213335

theorem tailTrace_4144818 : CollatzResearch.WordTrace tailWord_4144818 prefixEnd_4144818 2128283859407269614213335 := by
  unfold tailWord_4144818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37793482974509934850604777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100782621265359826268279405 37793482974509934850604777)
  ·
    refine ⟨28345112230882451137953583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37793482974509934850604777 28345112230882451137953583)
    ·
      refine ⟨42517668346323676706930375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28345112230882451137953583 42517668346323676706930375)
      ·
        refine ⟨63776502519485515060395563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42517668346323676706930375 63776502519485515060395563)
        ·
          refine ⟨95664753779228272590593345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63776502519485515060395563 95664753779228272590593345)
          ·
            refine ⟨71748565334421204442945009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95664753779228272590593345 71748565334421204442945009)
            ·
              refine ⟨53811424000815903332208757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71748565334421204442945009 53811424000815903332208757)
              ·
                refine ⟨5044821000076490937394571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53811424000815903332208757 5044821000076490937394571)
                ·
                  refine ⟨7567231500114736406091857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044821000076490937394571 7567231500114736406091857)
                  ·
                    refine ⟨5675423625086052304568893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567231500114736406091857 5675423625086052304568893)
                    ·
                      refine ⟨2128283859407269614213335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675423625086052304568893 2128283859407269614213335)
                      ·
                        rfl

theorem cell23_4144818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_4144818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144818 prefixEnd_4144818 := by exact prefixLift 4144818
  have htrace : WordTrace (prefixWord ++ tailWord_4144818) baseStart_4144818 baseEnd_4144818 := by
    simpa [prefixWord, tailWord_4144818, baseEnd_4144818] using wordTrace_append hprefix tailTrace_4144818
  have hstable : (prefixWord ++ tailWord_4144818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144818).length < 2 ^ (prefixWord ++ tailWord_4144818).sum := by decide
  have hdescent : baseEnd_4144818 < baseStart_4144818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144821 : List Nat := [1, 3, 3, 3, 2, 11]
def baseStart_4144821 : Nat := 118140960795 + 4144821 * 2 ^ 59
def prefixEnd_4144821 : Nat := 4983230072969 + 3 ^ 40 * 4144821 * 2
def baseEnd_4144821 : Nat := 8758376131066802890847

theorem tailTrace_4144821 : CollatzResearch.WordTrace tailWord_4144821 prefixEnd_4144821 8758376131066802890847 := by
  unfold tailWord_4144821
  simp only [CollatzResearch.WordTrace]
  refine ⟨151174041317028870914778317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100782694211352580609852211 151174041317028870914778317)
  ·
    refine ⟨56690265493885826593041869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151174041317028870914778317 56690265493885826593041869)
    ·
      refine ⟨21258849560207184972390701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56690265493885826593041869 21258849560207184972390701)
      ·
        refine ⟨7972068585077694364646513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21258849560207184972390701 7972068585077694364646513)
        ·
          refine ⟨5979051438808270773484885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7972068585077694364646513 5979051438808270773484885)
          ·
            refine ⟨8758376131066802890847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5979051438808270773484885 8758376131066802890847)
            ·
              rfl

theorem cell23_4144821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 11].length) (baseStart_4144821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144821 prefixEnd_4144821 := by exact prefixLift 4144821
  have htrace : WordTrace (prefixWord ++ tailWord_4144821) baseStart_4144821 baseEnd_4144821 := by
    simpa [prefixWord, tailWord_4144821, baseEnd_4144821] using wordTrace_append hprefix tailTrace_4144821
  have hstable : (prefixWord ++ tailWord_4144821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144821).length < 2 ^ (prefixWord ++ tailWord_4144821).sum := by decide
  have hdescent : baseEnd_4144821 < baseStart_4144821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144831 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 3]
def baseStart_4144831 : Nat := 118140960795 + 4144831 * 2 ^ 59
def prefixEnd_4144831 : Nat := 4983230072969 + 3 ^ 40 * 4144831 * 2
def baseEnd_4144831 : Nat := 2128290534655778063350775

theorem tailTrace_4144831 : CollatzResearch.WordTrace tailWord_4144831 prefixEnd_4144831 2128290534655778063350775 := by
  unfold tailWord_4144831
  simp only [CollatzResearch.WordTrace]
  refine ⟨151174406046992642622642347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100782937364661761748428231 151174406046992642622642347)
  ·
    refine ⟨226761609070488963933963521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151174406046992642622642347 226761609070488963933963521)
    ·
      refine ⟨170071206802866722950472641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226761609070488963933963521 170071206802866722950472641)
      ·
        refine ⟨127553405102150042212854481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170071206802866722950472641 127553405102150042212854481)
        ·
          refine ⟨95665053826612531659640861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127553405102150042212854481 95665053826612531659640861)
          ·
            refine ⟨35874395184979699372365323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95665053826612531659640861 35874395184979699372365323)
            ·
              refine ⟨53811592777469549058547985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35874395184979699372365323 53811592777469549058547985)
              ·
                refine ⟨40358694583102161793910989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53811592777469549058547985 40358694583102161793910989)
                ·
                  refine ⟨15134510468663310672716621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40358694583102161793910989 15134510468663310672716621)
                  ·
                    refine ⟨5675441425748741502268733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15134510468663310672716621 5675441425748741502268733)
                    ·
                      refine ⟨2128290534655778063350775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675441425748741502268733 2128290534655778063350775)
                      ·
                        rfl

theorem cell23_4144831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_4144831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144831 prefixEnd_4144831 := by exact prefixLift 4144831
  have htrace : WordTrace (prefixWord ++ tailWord_4144831) baseStart_4144831 baseEnd_4144831 := by
    simpa [prefixWord, tailWord_4144831, baseEnd_4144831] using wordTrace_append hprefix tailTrace_4144831
  have hstable : (prefixWord ++ tailWord_4144831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144831).length < 2 ^ (prefixWord ++ tailWord_4144831).sum := by decide
  have hdescent : baseEnd_4144831 < baseStart_4144831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144832 : List Nat := [2, 1, 1, 2, 4, 1, 3, 4, 1, 2, 2]
def baseStart_4144832 : Nat := 118140960795 + 4144832 * 2 ^ 59
def prefixEnd_4144832 : Nat := 4983230072969 + 3 ^ 40 * 4144832 * 2
def baseEnd_4144832 : Nat := 2128291048136432559438271

theorem tailTrace_4144832 : CollatzResearch.WordTrace tailWord_4144832 prefixEnd_4144832 2128291048136432559438271 := by
  unfold tailWord_4144832
  simp only [CollatzResearch.WordTrace]
  refine ⟨75587221259994509896714375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100782961679992679862285833 75587221259994509896714375)
  ·
    refine ⟨113380831889991764845071563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75587221259994509896714375 113380831889991764845071563)
    ·
      refine ⟨170071247834987647267607345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113380831889991764845071563 170071247834987647267607345)
      ·
        refine ⟨127553435876240735450705509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170071247834987647267607345 127553435876240735450705509)
        ·
          refine ⟨23916269226795137897007283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127553435876240735450705509 23916269226795137897007283)
          ·
            refine ⟨35874403840192706845510925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23916269226795137897007283 35874403840192706845510925)
            ·
              refine ⟨13452901440072265067066597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35874403840192706845510925 13452901440072265067066597)
              ·
                refine ⟨2522419020013549700074987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13452901440072265067066597 2522419020013549700074987)
                ·
                  refine ⟨3783628530020324550112481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522419020013549700074987 3783628530020324550112481)
                  ·
                    refine ⟨2837721397515243412584361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3783628530020324550112481 2837721397515243412584361)
                    ·
                      refine ⟨2128291048136432559438271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2837721397515243412584361 2128291048136432559438271)
                      ·
                        rfl

theorem cell23_4144832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_4144832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144832 prefixEnd_4144832 := by exact prefixLift 4144832
  have htrace : WordTrace (prefixWord ++ tailWord_4144832) baseStart_4144832 baseEnd_4144832 := by
    simpa [prefixWord, tailWord_4144832, baseEnd_4144832] using wordTrace_append hprefix tailTrace_4144832
  have hstable : (prefixWord ++ tailWord_4144832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144832).length < 2 ^ (prefixWord ++ tailWord_4144832).sum := by decide
  have hdescent : baseEnd_4144832 < baseStart_4144832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144845 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4144845 : Nat := 118140960795 + 4144845 * 2 ^ 59
def prefixEnd_4144845 : Nat := 4983230072969 + 3 ^ 40 * 4144845 * 2
def baseEnd_4144845 : Nat := 2128297723384941008575711

theorem tailTrace_4144845 : CollatzResearch.WordTrace tailWord_4144845 prefixEnd_4144845 2128297723384941008575711 := by
  unfold tailWord_4144845
  simp only [CollatzResearch.WordTrace]
  refine ⟨151174916668941923013651989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100783277779294615342434659 151174916668941923013651989)
  ·
    refine ⟨7086324218856652641264937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151174916668941923013651989 7086324218856652641264937)
    ·
      refine ⟨5314743164142489480948703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7086324218856652641264937 5314743164142489480948703)
      ·
        refine ⟨7972114746213734221423055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314743164142489480948703 7972114746213734221423055)
        ·
          refine ⟨11958172119320601332134583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972114746213734221423055 11958172119320601332134583)
          ·
            refine ⟨17937258178980901998201875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958172119320601332134583 17937258178980901998201875)
            ·
              refine ⟨26905887268471352997302813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17937258178980901998201875 26905887268471352997302813)
              ·
                refine ⟨10089707725676757373988555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26905887268471352997302813 10089707725676757373988555)
                ·
                  refine ⟨15134561588515136060982833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089707725676757373988555 15134561588515136060982833)
                  ·
                    refine ⟨11350921191386352045737125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15134561588515136060982833 11350921191386352045737125)
                    ·
                      refine ⟨2128297723384941008575711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11350921191386352045737125 2128297723384941008575711)
                      ·
                        rfl

theorem cell23_4144845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4144845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144845 prefixEnd_4144845 := by exact prefixLift 4144845
  have htrace : WordTrace (prefixWord ++ tailWord_4144845) baseStart_4144845 baseEnd_4144845 := by
    simpa [prefixWord, tailWord_4144845, baseEnd_4144845] using wordTrace_append hprefix tailTrace_4144845
  have hstable : (prefixWord ++ tailWord_4144845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144845).length < 2 ^ (prefixWord ++ tailWord_4144845).sum := by decide
  have hdescent : baseEnd_4144845 < baseStart_4144845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144881 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 2, 6]
def baseStart_4144881 : Nat := 118140960795 + 4144881 * 2 ^ 59
def prefixEnd_4144881 : Nat := 4983230072969 + 3 ^ 40 * 4144881 * 2
def baseEnd_4144881 : Nat := 709438736229500955908515

theorem tailTrace_4144881 : CollatzResearch.WordTrace tailWord_4144881 prefixEnd_4144881 709438736229500955908515 := by
  unfold tailWord_4144881
  simp only [CollatzResearch.WordTrace]
  refine ⟨151176229696811501161962497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100784153131207667441308331 151176229696811501161962497)
  ·
    refine ⟨113382172272608625871471873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151176229696811501161962497 113382172272608625871471873)
    ·
      refine ⟨85036629204456469403603905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113382172272608625871471873 85036629204456469403603905)
      ·
        refine ⟨63777471903342352052702929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85036629204456469403603905 63777471903342352052702929)
        ·
          refine ⟨47833103927506764039527197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63777471903342352052702929 47833103927506764039527197)
          ·
            refine ⟨17937413972815036514822699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47833103927506764039527197 17937413972815036514822699)
            ·
              refine ⟨26906120959222554772234049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17937413972815036514822699 26906120959222554772234049)
              ·
                refine ⟨20179590719416916079175537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26906120959222554772234049 20179590719416916079175537)
                ·
                  refine ⟨15134693039562687059381653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20179590719416916079175537 15134693039562687059381653)
                  ·
                    refine ⟨709438736229500955908515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15134693039562687059381653 709438736229500955908515)
                    ·
                      rfl

theorem cell23_4144881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_4144881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144881 prefixEnd_4144881 := by exact prefixLift 4144881
  have htrace : WordTrace (prefixWord ++ tailWord_4144881) baseStart_4144881 baseEnd_4144881 := by
    simpa [prefixWord, tailWord_4144881, baseEnd_4144881] using wordTrace_append hprefix tailTrace_4144881
  have hstable : (prefixWord ++ tailWord_4144881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144881).length < 2 ^ (prefixWord ++ tailWord_4144881).sum := by decide
  have hdescent : baseEnd_4144881 < baseStart_4144881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144891 : List Nat := [1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 3]
def baseStart_4144891 : Nat := 118140960795 + 4144891 * 2 ^ 59
def prefixEnd_4144891 : Nat := 4983230072969 + 3 ^ 40 * 4144891 * 2
def baseEnd_4144891 : Nat := 2128321343495047828600499

theorem tailTrace_4144891 : CollatzResearch.WordTrace tailWord_4144891 prefixEnd_4144891 2128321343495047828600499 := by
  unfold tailWord_4144891
  simp only [CollatzResearch.WordTrace]
  refine ⟨151176594426775272869826527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100784396284516848579884351 151176594426775272869826527)
  ·
    refine ⟨226764891640162909304739791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151176594426775272869826527 226764891640162909304739791)
    ·
      refine ⟨340147337460244363957109687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226764891640162909304739791 340147337460244363957109687)
      ·
        refine ⟨510221006190366545935664531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340147337460244363957109687 510221006190366545935664531)
        ·
          refine ⟨765331509285549818903496797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510221006190366545935664531 765331509285549818903496797)
          ·
            refine ⟨286999315982081182088811299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765331509285549818903496797 286999315982081182088811299)
            ·
              refine ⟨430498973973121773133216949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286999315982081182088811299 430498973973121773133216949)
              ·
                refine ⟨40359278809980166231239089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 430498973973121773133216949 40359278809980166231239089)
                ·
                  refine ⟨30269459107485124673429317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40359278809980166231239089 30269459107485124673429317)
                  ·
                    refine ⟨5675523582653460876267997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30269459107485124673429317 5675523582653460876267997)
                    ·
                      refine ⟨2128321343495047828600499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675523582653460876267997 2128321343495047828600499)
                      ·
                        rfl

theorem cell23_4144891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 4, 3].length) (baseStart_4144891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144891 prefixEnd_4144891 := by exact prefixLift 4144891
  have htrace : WordTrace (prefixWord ++ tailWord_4144891) baseStart_4144891 baseEnd_4144891 := by
    simpa [prefixWord, tailWord_4144891, baseEnd_4144891] using wordTrace_append hprefix tailTrace_4144891
  have hstable : (prefixWord ++ tailWord_4144891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144891).length < 2 ^ (prefixWord ++ tailWord_4144891).sum := by decide
  have hdescent : baseEnd_4144891 < baseStart_4144891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4144898 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4144898 : Nat := 118140960795 + 4144898 * 2 ^ 59
def prefixEnd_4144898 : Nat := 4983230072969 + 3 ^ 40 * 4144898 * 2
def baseEnd_4144898 : Nat := 709441645953209767070989

theorem tailTrace_4144898 : CollatzResearch.WordTrace tailWord_4144898 prefixEnd_4144898 709441645953209767070989 := by
  unfold tailWord_4144898
  simp only [CollatzResearch.WordTrace]
  refine ⟨37794212434437478266332837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100784566491833275376887565 37794212434437478266332837)
  ·
    refine ⟨7086414831457027174937407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37794212434437478266332837 7086414831457027174937407)
    ·
      refine ⟨10629622247185540762406111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086414831457027174937407 10629622247185540762406111)
      ·
        refine ⟨15944433370778311143609167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10629622247185540762406111 15944433370778311143609167)
        ·
          refine ⟨23916650056167466715413751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944433370778311143609167 23916650056167466715413751)
          ·
            refine ⟨35874975084251200073120627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23916650056167466715413751 35874975084251200073120627)
            ·
              refine ⟨53812462626376800109680941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35874975084251200073120627 53812462626376800109680941)
              ·
                refine ⟨20179673484891300041130353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53812462626376800109680941 20179673484891300041130353)
                ·
                  refine ⟨15134755113668475030847765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20179673484891300041130353 15134755113668475030847765)
                  ·
                    refine ⟨709441645953209767070989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15134755113668475030847765 709441645953209767070989)
                    ·
                      rfl

theorem cell23_4144898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4144898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4144898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4144898 prefixEnd_4144898 := by exact prefixLift 4144898
  have htrace : WordTrace (prefixWord ++ tailWord_4144898) baseStart_4144898 baseEnd_4144898 := by
    simpa [prefixWord, tailWord_4144898, baseEnd_4144898] using wordTrace_append hprefix tailTrace_4144898
  have hstable : (prefixWord ++ tailWord_4144898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4144898).length < 2 ^ (prefixWord ++ tailWord_4144898).sum := by decide
  have hdescent : baseEnd_4144898 < baseStart_4144898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4144898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145001 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 8]
def baseStart_4145001 : Nat := 118140960795 + 4145001 * 2 ^ 59
def prefixEnd_4145001 : Nat := 4983230072969 + 3 ^ 40 * 4145001 * 2
def baseEnd_4145001 : Nat := 236486425151893599802777

theorem tailTrace_4145001 : CollatzResearch.WordTrace tailWord_4145001 prefixEnd_4145001 236486425151893599802777 := by
  unfold tailWord_4145001
  simp only [CollatzResearch.WordTrace]
  refine ⟨151180606456376761656330857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100787070970917841104220571 151180606456376761656330857)
  ·
    refine ⟨113385454842282571242248143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151180606456376761656330857 113385454842282571242248143)
    ·
      refine ⟨170078182263423856863372215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113385454842282571242248143 170078182263423856863372215)
      ·
        refine ⟨255117273395135785295058323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170078182263423856863372215 255117273395135785295058323)
        ·
          refine ⟨382675910092703677942587485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255117273395135785295058323 382675910092703677942587485)
          ·
            refine ⟨143503466284763879228470307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382675910092703677942587485 143503466284763879228470307)
            ·
              refine ⟨215255199427145818842705461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143503466284763879228470307 215255199427145818842705461)
              ·
                refine ⟨20180174946294920516503637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215255199427145818842705461 20180174946294920516503637)
                ·
                  refine ⟨236486425151893599802777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20180174946294920516503637 236486425151893599802777)
                  ·
                    rfl

theorem cell23_4145001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_4145001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145001 prefixEnd_4145001 := by exact prefixLift 4145001
  have htrace : WordTrace (prefixWord ++ tailWord_4145001) baseStart_4145001 baseEnd_4145001 := by
    simpa [prefixWord, tailWord_4145001, baseEnd_4145001] using wordTrace_append hprefix tailTrace_4145001
  have hstable : (prefixWord ++ tailWord_4145001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145001).length < 2 ^ (prefixWord ++ tailWord_4145001).sum := by decide
  have hdescent : baseEnd_4145001 < baseStart_4145001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145018 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_4145018 : Nat := 118140960795 + 4145018 * 2 ^ 59
def prefixEnd_4145018 : Nat := 4983230072969 + 3 ^ 40 * 4145018 * 2
def baseEnd_4145018 : Nat := 236487395059796536856935

theorem tailTrace_4145018 : CollatzResearch.WordTrace tailWord_4145018 prefixEnd_4145018 236487395059796536856935 := by
  unfold tailWord_4145018
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795306624328793389924927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100787484331543449039799805 37795306624328793389924927)
  ·
    refine ⟨56692959936493190084887391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37795306624328793389924927 56692959936493190084887391)
    ·
      refine ⟨85039439904739785127331087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56692959936493190084887391 85039439904739785127331087)
      ·
        refine ⟨127559159857109677690996631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85039439904739785127331087 127559159857109677690996631)
        ·
          refine ⟨191338739785664516536494947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127559159857109677690996631 191338739785664516536494947)
          ·
            refine ⟨287008109678496774804742421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191338739785664516536494947 287008109678496774804742421)
            ·
              refine ⟨13453505141179536318972301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287008109678496774804742421 13453505141179536318972301)
              ·
                refine ⟨5045064427942326119614613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13453505141179536318972301 5045064427942326119614613)
                ·
                  refine ⟨236487395059796536856935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5045064427942326119614613 236487395059796536856935)
                  ·
                    rfl

theorem cell23_4145018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_4145018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145018 prefixEnd_4145018 := by exact prefixLift 4145018
  have htrace : WordTrace (prefixWord ++ tailWord_4145018) baseStart_4145018 baseEnd_4145018 := by
    simpa [prefixWord, tailWord_4145018, baseEnd_4145018] using wordTrace_append hprefix tailTrace_4145018
  have hstable : (prefixWord ++ tailWord_4145018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145018).length < 2 ^ (prefixWord ++ tailWord_4145018).sum := by decide
  have hdescent : baseEnd_4145018 < baseStart_4145018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145022 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4145022 : Nat := 118140960795 + 4145022 * 2 ^ 59
def prefixEnd_4145022 : Nat := 4983230072969 + 3 ^ 40 * 4145022 * 2
def baseEnd_4145022 : Nat := 709462869820262272020799

theorem tailTrace_4145022 : CollatzResearch.WordTrace tailWord_4145022 prefixEnd_4145022 709462869820262272020799 := by
  unfold tailWord_4145022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18897671548662585280355665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100787581592867121495230213 18897671548662585280355665)
  ·
    refine ⟨14173253661496938960266749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18897671548662585280355665 14173253661496938960266749)
    ·
      refine ⟨5314970123061352110100031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14173253661496938960266749 5314970123061352110100031)
      ·
        refine ⟨7972455184592028165150047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314970123061352110100031 7972455184592028165150047)
        ·
          refine ⟨11958682776888042247725071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972455184592028165150047 11958682776888042247725071)
          ·
            refine ⟨17938024165332063371587607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958682776888042247725071 17938024165332063371587607)
            ·
              refine ⟨26907036247998095057381411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17938024165332063371587607 26907036247998095057381411)
              ·
                refine ⟨40360554371997142586072117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26907036247998095057381411 40360554371997142586072117)
                ·
                  refine ⟨3783801972374732117444261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40360554371997142586072117 3783801972374732117444261)
                  ·
                    refine ⟨709462869820262272020799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3783801972374732117444261 709462869820262272020799)
                    ·
                      rfl

theorem cell23_4145022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4145022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145022 prefixEnd_4145022 := by exact prefixLift 4145022
  have htrace : WordTrace (prefixWord ++ tailWord_4145022) baseStart_4145022 baseEnd_4145022 := by
    simpa [prefixWord, tailWord_4145022, baseEnd_4145022] using wordTrace_append hprefix tailTrace_4145022
  have hstable : (prefixWord ++ tailWord_4145022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145022).length < 2 ^ (prefixWord ++ tailWord_4145022).sum := by decide
  have hdescent : baseEnd_4145022 < baseStart_4145022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145045 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_4145045 : Nat := 118140960795 + 4145045 * 2 ^ 59
def prefixEnd_4145045 : Nat := 4983230072969 + 3 ^ 40 * 4145045 * 2
def baseEnd_4145045 : Nat := 2128400419515840226074791

theorem tailTrace_4145045 : CollatzResearch.WordTrace tailWord_4145045 prefixEnd_4145045 2128400419515840226074791 := by
  unfold tailWord_4145045
  simp only [CollatzResearch.WordTrace]
  refine ⟨151182211268217357170932589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100788140845478238113955059 151182211268217357170932589)
  ·
    refine ⟨56693329225581508939099721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151182211268217357170932589 56693329225581508939099721)
    ·
      refine ⟨42519996919186131704324791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56693329225581508939099721 42519996919186131704324791)
      ·
        refine ⟨63779995378779197556487187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42519996919186131704324791 63779995378779197556487187)
        ·
          refine ⟨95669993068168796334730781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63779995378779197556487187 95669993068168796334730781)
          ·
            refine ⟨35876247400563298625524043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95669993068168796334730781 35876247400563298625524043)
            ·
              refine ⟨53814371100844947938286065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35876247400563298625524043 53814371100844947938286065)
              ·
                refine ⟨40360778325633710953714549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53814371100844947938286065 40360778325633710953714549)
                ·
                  refine ⟨3783822968028160401910739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40360778325633710953714549 3783822968028160401910739)
                  ·
                    refine ⟨5675734452042240602866109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3783822968028160401910739 5675734452042240602866109)
                    ·
                      refine ⟨2128400419515840226074791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675734452042240602866109 2128400419515840226074791)
                      ·
                        rfl

theorem cell23_4145045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_4145045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145045 prefixEnd_4145045 := by exact prefixLift 4145045
  have htrace : WordTrace (prefixWord ++ tailWord_4145045) baseStart_4145045 baseEnd_4145045 := by
    simpa [prefixWord, tailWord_4145045, baseEnd_4145045] using wordTrace_append hprefix tailTrace_4145045
  have hstable : (prefixWord ++ tailWord_4145045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145045).length < 2 ^ (prefixWord ++ tailWord_4145045).sum := by decide
  have hdescent : baseEnd_4145045 < baseStart_4145045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145052 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 6]
def baseStart_4145052 : Nat := 118140960795 + 4145052 * 2 ^ 59
def prefixEnd_4145052 : Nat := 4983230072969 + 3 ^ 40 * 4145052 * 2
def baseEnd_4145052 : Nat := 236489334875602410965251

theorem tailTrace_4145052 : CollatzResearch.WordTrace tailWord_4145052 prefixEnd_4145052 236489334875602410965251 := by
  unfold tailWord_4145052
  simp only [CollatzResearch.WordTrace]
  refine ⟨75591233289595998683218705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100788311052794664910958273 75591233289595998683218705)
  ·
    refine ⟨56693424967196999012414029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75591233289595998683218705 56693424967196999012414029)
    ·
      refine ⟨21260034362698874629655261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56693424967196999012414029 21260034362698874629655261)
      ·
        refine ⟨7972512886012077986120723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21260034362698874629655261 7972512886012077986120723)
        ·
          refine ⟨11958769329018116979181085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972512886012077986120723 11958769329018116979181085)
          ·
            refine ⟨4484538498381793867192907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11958769329018116979181085 4484538498381793867192907)
            ·
              refine ⟨6726807747572690800789361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484538498381793867192907 6726807747572690800789361)
              ·
                refine ⟨5045105810679518100592021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726807747572690800789361 5045105810679518100592021)
                ·
                  refine ⟨236489334875602410965251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5045105810679518100592021 236489334875602410965251)
                  ·
                    rfl

theorem cell23_4145052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 6].length) (baseStart_4145052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145052 prefixEnd_4145052 := by exact prefixLift 4145052
  have htrace : WordTrace (prefixWord ++ tailWord_4145052) baseStart_4145052 baseEnd_4145052 := by
    simpa [prefixWord, tailWord_4145052, baseEnd_4145052] using wordTrace_append hprefix tailTrace_4145052
  have hstable : (prefixWord ++ tailWord_4145052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145052).length < 2 ^ (prefixWord ++ tailWord_4145052).sum := by decide
  have hdescent : baseEnd_4145052 < baseStart_4145052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145088 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5]
def baseStart_4145088 : Nat := 118140960795 + 4145088 * 2 ^ 59
def prefixEnd_4145088 : Nat := 4983230072969 + 3 ^ 40 * 4145088 * 2
def baseEnd_4145088 : Nat := 2128422499183983557837093

theorem tailTrace_4145088 : CollatzResearch.WordTrace tailWord_4145088 prefixEnd_4145088 2128422499183983557837093 := by
  unfold tailWord_4145088
  simp only [CollatzResearch.WordTrace]
  refine ⟨75591889803530787757373959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100789186404707717009831945 75591889803530787757373959)
  ·
    refine ⟨113387834705296181636060939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75591889803530787757373959 113387834705296181636060939)
    ·
      refine ⟨170081752057944272454091409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113387834705296181636060939 170081752057944272454091409)
      ·
        refine ⟨127561314043458204340568557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170081752057944272454091409 127561314043458204340568557)
        ·
          refine ⟨47835492766296826627713209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127561314043458204340568557 47835492766296826627713209)
          ·
            refine ⟨35876619574722619970784907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47835492766296826627713209 35876619574722619970784907)
            ·
              refine ⟨53814929362083929956177361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35876619574722619970784907 53814929362083929956177361)
              ·
                refine ⟨40361197021562947467133021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53814929362083929956177361 40361197021562947467133021)
                ·
                  refine ⟨15135448883086105300174883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40361197021562947467133021 15135448883086105300174883)
                  ·
                    refine ⟨22703173324629157950262325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15135448883086105300174883 22703173324629157950262325)
                    ·
                      refine ⟨2128422499183983557837093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22703173324629157950262325 2128422499183983557837093)
                      ·
                        rfl

theorem cell23_4145088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_4145088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145088 prefixEnd_4145088 := by exact prefixLift 4145088
  have htrace : WordTrace (prefixWord ++ tailWord_4145088) baseStart_4145088 baseEnd_4145088 := by
    simpa [prefixWord, tailWord_4145088, baseEnd_4145088] using wordTrace_append hprefix tailTrace_4145088
  have hstable : (prefixWord ++ tailWord_4145088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145088).length < 2 ^ (prefixWord ++ tailWord_4145088).sum := by decide
  have hdescent : baseEnd_4145088 < baseStart_4145088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145096 : List Nat := [2, 1, 3, 1, 4, 3, 1, 3, 1, 1, 3]
def baseStart_4145096 : Nat := 118140960795 + 4145096 * 2 ^ 59
def prefixEnd_4145096 : Nat := 4983230072969 + 3 ^ 40 * 4145096 * 2
def baseEnd_4145096 : Nat := 2128426607029219526537057

theorem tailTrace_4145096 : CollatzResearch.WordTrace tailWord_4145096 prefixEnd_4145096 2128426607029219526537057 := by
  unfold tailWord_4145096
  simp only [CollatzResearch.WordTrace]
  refine ⟨75592035695516296440519571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100789380927355061920692761 75592035695516296440519571)
  ·
    refine ⟨113388053543274444660779357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75592035695516296440519571 113388053543274444660779357)
    ·
      refine ⟨42520520078727916747792259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113388053543274444660779357 42520520078727916747792259)
      ·
        refine ⟨63780780118091875121688389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42520520078727916747792259 63780780118091875121688389)
        ·
          refine ⟨11958896272142226585316573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63780780118091875121688389 11958896272142226585316573)
          ·
            refine ⟨4484586102053334969493715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11958896272142226585316573 4484586102053334969493715)
            ·
              refine ⟨6726879153080002454240573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484586102053334969493715 6726879153080002454240573)
              ·
                refine ⟨2522579682405000920340215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6726879153080002454240573 2522579682405000920340215)
                ·
                  refine ⟨3783869523607501380510323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522579682405000920340215 3783869523607501380510323)
                  ·
                    refine ⟨5675804285411252070765485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3783869523607501380510323 5675804285411252070765485)
                    ·
                      refine ⟨2128426607029219526537057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675804285411252070765485 2128426607029219526537057)
                      ·
                        rfl

theorem cell23_4145096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 1, 1, 3].length) (baseStart_4145096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145096 prefixEnd_4145096 := by exact prefixLift 4145096
  have htrace : WordTrace (prefixWord ++ tailWord_4145096) baseStart_4145096 baseEnd_4145096 := by
    simpa [prefixWord, tailWord_4145096, baseEnd_4145096] using wordTrace_append hprefix tailTrace_4145096
  have hstable : (prefixWord ++ tailWord_4145096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145096).length < 2 ^ (prefixWord ++ tailWord_4145096).sum := by decide
  have hdescent : baseEnd_4145096 < baseStart_4145096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145119 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 3, 2, 2]
def baseStart_4145119 : Nat := 118140960795 + 4145119 * 2 ^ 59
def prefixEnd_4145119 : Nat := 4983230072969 + 3 ^ 40 * 4145119 * 2
def baseEnd_4145119 : Nat := 2128438417084272936549451

theorem tailTrace_4145119 : CollatzResearch.WordTrace tailWord_4145119 prefixEnd_4145119 2128438417084272936549451 := by
  unfold tailWord_4145119
  simp only [CollatzResearch.WordTrace]
  refine ⟨151184910269949267809126411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100789940179966178539417607 151184910269949267809126411)
  ·
    refine ⟨226777365404923901713689617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151184910269949267809126411 226777365404923901713689617)
    ·
      refine ⟨170083024053692926285267213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226777365404923901713689617 170083024053692926285267213)
      ·
        refine ⟨63781134020134847356975205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170083024053692926285267213 63781134020134847356975205)
        ·
          refine ⟨11958962628775283879432851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63781134020134847356975205 11958962628775283879432851)
          ·
            refine ⟨17938443943162925819149277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958962628775283879432851 17938443943162925819149277)
            ·
              refine ⟨6726916478686097182180979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17938443943162925819149277 6726916478686097182180979)
              ·
                refine ⟨10090374718029145773271469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726916478686097182180979 10090374718029145773271469)
                ·
                  refine ⟨3783890519260929664976801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10090374718029145773271469 3783890519260929664976801)
                  ·
                    refine ⟨2837917889445697248732601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3783890519260929664976801 2837917889445697248732601)
                    ·
                      refine ⟨2128438417084272936549451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2837917889445697248732601 2128438417084272936549451)
                      ·
                        rfl

theorem cell23_4145119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_4145119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145119 prefixEnd_4145119 := by exact prefixLift 4145119
  have htrace : WordTrace (prefixWord ++ tailWord_4145119) baseStart_4145119 baseEnd_4145119 := by
    simpa [prefixWord, tailWord_4145119, baseEnd_4145119] using wordTrace_append hprefix tailTrace_4145119
  have hstable : (prefixWord ++ tailWord_4145119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145119).length < 2 ^ (prefixWord ++ tailWord_4145119).sum := by decide
  have hdescent : baseEnd_4145119 < baseStart_4145119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145128 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_4145128 : Nat := 118140960795 + 4145128 * 2 ^ 59
def prefixEnd_4145128 : Nat := 4983230072969 + 3 ^ 40 * 4145128 * 2
def baseEnd_4145128 : Nat := 2128443038410163401336909

theorem tailTrace_4145128 : CollatzResearch.WordTrace tailWord_4145128 prefixEnd_4145128 2128443038410163401336909 := by
  unfold tailWord_4145128
  simp only [CollatzResearch.WordTrace]
  refine ⟨75592619263458331173102019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100790159017944441564136025 75592619263458331173102019)
  ·
    refine ⟨113388928895187496759653029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75592619263458331173102019 113388928895187496759653029)
    ·
      refine ⟨21260424167847655642434943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113388928895187496759653029 21260424167847655642434943)
      ·
        refine ⟨31890636251771483463652415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21260424167847655642434943 31890636251771483463652415)
        ·
          refine ⟨47835954377657225195478623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31890636251771483463652415 47835954377657225195478623)
          ·
            refine ⟨71753931566485837793217935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47835954377657225195478623 71753931566485837793217935)
            ·
              refine ⟨107630897349728756689826903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71753931566485837793217935 107630897349728756689826903)
              ·
                refine ⟨161446346024593135034740355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107630897349728756689826903 161446346024593135034740355)
                ·
                  refine ⟨242169519036889702552110533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161446346024593135034740355 242169519036889702552110533)
                  ·
                    refine ⟨45406784819416819228520725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 242169519036889702552110533 45406784819416819228520725)
                    ·
                      refine ⟨2128443038410163401336909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45406784819416819228520725 2128443038410163401336909)
                      ·
                        rfl

theorem cell23_4145128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_4145128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145128 prefixEnd_4145128 := by exact prefixLift 4145128
  have htrace : WordTrace (prefixWord ++ tailWord_4145128) baseStart_4145128 baseEnd_4145128 := by
    simpa [prefixWord, tailWord_4145128, baseEnd_4145128] using wordTrace_append hprefix tailTrace_4145128
  have hstable : (prefixWord ++ tailWord_4145128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145128).length < 2 ^ (prefixWord ++ tailWord_4145128).sum := by decide
  have hdescent : baseEnd_4145128 < baseStart_4145128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145135 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 3]
def baseStart_4145135 : Nat := 118140960795 + 4145135 * 2 ^ 59
def prefixEnd_4145135 : Nat := 4983230072969 + 3 ^ 40 * 4145135 * 2
def baseEnd_4145135 : Nat := 2128446632774744873949377

theorem tailTrace_4145135 : CollatzResearch.WordTrace tailWord_4145135 prefixEnd_4145135 2128446632774744873949377 := by
  unfold tailWord_4145135
  simp only [CollatzResearch.WordTrace]
  refine ⟨151185493837891302541708859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100790329225260868361139239 151185493837891302541708859)
  ·
    refine ⟨226778240756836953812563289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151185493837891302541708859 226778240756836953812563289)
    ·
      refine ⟨170083680567627715359422467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226778240756836953812563289 170083680567627715359422467)
      ·
        refine ⟨255125520851441573039133701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170083680567627715359422467 255125520851441573039133701)
        ·
          refine ⟨47836035159645294944837569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255125520851441573039133701 47836035159645294944837569)
          ·
            refine ⟨35877026369733971208628177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47836035159645294944837569 35877026369733971208628177)
            ·
              refine ⟨26907769777300478406471133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35877026369733971208628177 26907769777300478406471133)
              ·
                refine ⟨10090413666487679402426675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26907769777300478406471133 10090413666487679402426675)
                ·
                  refine ⟨15135620499731519103640013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090413666487679402426675 15135620499731519103640013)
                  ·
                    refine ⟨5675857687399319663865005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15135620499731519103640013 5675857687399319663865005)
                    ·
                      refine ⟨2128446632774744873949377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675857687399319663865005 2128446632774744873949377)
                      ·
                        rfl

theorem cell23_4145135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 3].length) (baseStart_4145135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145135 prefixEnd_4145135 := by exact prefixLift 4145135
  have htrace : WordTrace (prefixWord ++ tailWord_4145135) baseStart_4145135 baseEnd_4145135 := by
    simpa [prefixWord, tailWord_4145135, baseEnd_4145135] using wordTrace_append hprefix tailTrace_4145135
  have hstable : (prefixWord ++ tailWord_4145135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145135).length < 2 ^ (prefixWord ++ tailWord_4145135).sum := by decide
  have hdescent : baseEnd_4145135 < baseStart_4145135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145156 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_4145156 : Nat := 118140960795 + 4145156 * 2 ^ 59
def prefixEnd_4145156 : Nat := 4983230072969 + 3 ^ 40 * 4145156 * 2
def baseEnd_4145156 : Nat := 2128457415868489291786781

theorem tailTrace_4145156 : CollatzResearch.WordTrace tailWord_4145156 prefixEnd_4145156 2128457415868489291786781 := by
  unfold tailWord_4145156
  simp only [CollatzResearch.WordTrace]
  refine ⟨75593129885407611564111661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100790839847210148752148881 75593129885407611564111661)
  ·
    refine ⟨28347423707027854336541873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75593129885407611564111661 28347423707027854336541873)
    ·
      refine ⟨21260567780270890752406405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28347423707027854336541873 21260567780270890752406405)
      ·
        refine ⟨3986356458800792016076201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21260567780270890752406405 3986356458800792016076201)
        ·
          refine ⟨2989767344100594012057151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3986356458800792016076201 2989767344100594012057151)
          ·
            refine ⟨4484651016150891018085727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2989767344100594012057151 4484651016150891018085727)
            ·
              refine ⟨6726976524226336527128591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4484651016150891018085727 6726976524226336527128591)
              ·
                refine ⟨10090464786339504790692887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726976524226336527128591 10090464786339504790692887)
                ·
                  refine ⟨15135697179509257186039331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090464786339504790692887 15135697179509257186039331)
                  ·
                    refine ⟨22703545769263885779058997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15135697179509257186039331 22703545769263885779058997)
                    ·
                      refine ⟨2128457415868489291786781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22703545769263885779058997 2128457415868489291786781)
                      ·
                        rfl

theorem cell23_4145156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_4145156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145156 prefixEnd_4145156 := by exact prefixLift 4145156
  have htrace : WordTrace (prefixWord ++ tailWord_4145156) baseStart_4145156 baseEnd_4145156 := by
    simpa [prefixWord, tailWord_4145156, baseEnd_4145156] using wordTrace_append hprefix tailTrace_4145156
  have hstable : (prefixWord ++ tailWord_4145156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145156).length < 2 ^ (prefixWord ++ tailWord_4145156).sum := by decide
  have hdescent : baseEnd_4145156 < baseStart_4145156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145168 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 4, 6]
def baseStart_4145168 : Nat := 118140960795 + 4145168 * 2 ^ 59
def prefixEnd_4145168 : Nat := 4983230072969 + 3 ^ 40 * 4145168 * 2
def baseEnd_4145168 : Nat := 709487859212114414945575

theorem tailTrace_4145168 : CollatzResearch.WordTrace tailWord_4145168 prefixEnd_4145168 709487859212114414945575 := by
  unfold tailWord_4145168
  simp only [CollatzResearch.WordTrace]
  refine ⟨75593348723385874588830079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100791131631181166118440105 75593348723385874588830079)
  ·
    refine ⟨113390023085078811883245119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75593348723385874588830079 113390023085078811883245119)
    ·
      refine ⟨170085034627618217824867679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113390023085078811883245119 170085034627618217824867679)
      ·
        refine ⟨255127551941427326737301519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170085034627618217824867679 255127551941427326737301519)
        ·
          refine ⟨382691327912140990105952279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255127551941427326737301519 382691327912140990105952279)
          ·
            refine ⟨574036991868211485158928419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382691327912140990105952279 574036991868211485158928419)
            ·
              refine ⟨861055487802317227738392629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574036991868211485158928419 861055487802317227738392629)
              ·
                refine ⟨80723951981467240100474309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 861055487802317227738392629 80723951981467240100474309)
                ·
                  refine ⟨15135740996525107518838933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80723951981467240100474309 15135740996525107518838933)
                  ·
                    refine ⟨709487859212114414945575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15135740996525107518838933 709487859212114414945575)
                    ·
                      rfl

theorem cell23_4145168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 6].length) (baseStart_4145168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145168 prefixEnd_4145168 := by exact prefixLift 4145168
  have htrace : WordTrace (prefixWord ++ tailWord_4145168) baseStart_4145168 baseEnd_4145168 := by
    simpa [prefixWord, tailWord_4145168, baseEnd_4145168] using wordTrace_append hprefix tailTrace_4145168
  have hstable : (prefixWord ++ tailWord_4145168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145168).length < 2 ^ (prefixWord ++ tailWord_4145168).sum := by decide
  have hdescent : baseEnd_4145168 < baseStart_4145168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145225 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_4145225 : Nat := 118140960795 + 4145225 * 2 ^ 59
def prefixEnd_4145225 : Nat := 4983230072969 + 3 ^ 40 * 4145225 * 2
def baseEnd_4145225 : Nat := 2128492846033649521823963

theorem tailTrace_4145225 : CollatzResearch.WordTrace tailWord_4145225 prefixEnd_4145225 2128492846033649521823963 := by
  unfold tailWord_4145225
  simp only [CollatzResearch.WordTrace]
  refine ⟨151188776407565247912485129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100792517605043498608323419 151188776407565247912485129)
  ·
    refine ⟨113391582305673935934363847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151188776407565247912485129 113391582305673935934363847)
    ·
      refine ⟨170087373458510903901545771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113391582305673935934363847 170087373458510903901545771)
      ·
        refine ⟨255131060187766355852318657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170087373458510903901545771 255131060187766355852318657)
        ·
          refine ⟨191348295140824766889238993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255131060187766355852318657 191348295140824766889238993)
          ·
            refine ⟨143511221355618575166929245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191348295140824766889238993 143511221355618575166929245)
            ·
              refine ⟨53816708008356965687598467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143511221355618575166929245 53816708008356965687598467)
              ·
                refine ⟨80725062012535448531397701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53816708008356965687598467 80725062012535448531397701)
                ·
                  refine ⟨15135949127350396599637069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80725062012535448531397701 15135949127350396599637069)
                  ·
                    refine ⟨5675980922756398724863901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15135949127350396599637069 5675980922756398724863901)
                    ·
                      refine ⟨2128492846033649521823963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5675980922756398724863901 2128492846033649521823963)
                      ·
                        rfl

theorem cell23_4145225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_4145225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145225 prefixEnd_4145225 := by exact prefixLift 4145225
  have htrace : WordTrace (prefixWord ++ tailWord_4145225) baseStart_4145225 baseEnd_4145225 := by
    simpa [prefixWord, tailWord_4145225, baseEnd_4145225] using wordTrace_append hprefix tailTrace_4145225
  have hstable : (prefixWord ++ tailWord_4145225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145225).length < 2 ^ (prefixWord ++ tailWord_4145225).sum := by decide
  have hdescent : baseEnd_4145225 < baseStart_4145225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145252 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 2, 5, 2]
def baseStart_4145252 : Nat := 118140960795 + 4145252 * 2 ^ 59
def prefixEnd_4145252 : Nat := 4983230072969 + 3 ^ 40 * 4145252 * 2
def baseEnd_4145252 : Nat := 2128506710011320916186339

theorem tailTrace_4145252 : CollatzResearch.WordTrace tailWord_4145252 prefixEnd_4145252 2128506710011320916186339 := by
  unfold tailWord_4145252
  simp only [CollatzResearch.WordTrace]
  refine ⟨75594880589233715761859005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100793174118978287682478673 75594880589233715761859005)
  ·
    refine ⟨28348080220962643410697127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75594880589233715761859005 28348080220962643410697127)
    ·
      refine ⟨42522120331443965116045691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28348080220962643410697127 42522120331443965116045691)
      ·
        refine ⟨63783180497165947674068537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42522120331443965116045691 63783180497165947674068537)
        ·
          refine ⟨47837385372874460755551403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63783180497165947674068537 47837385372874460755551403)
          ·
            refine ⟨71756078059311691133327105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47837385372874460755551403 71756078059311691133327105)
            ·
              refine ⟨53817058544483768349995329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71756078059311691133327105 53817058544483768349995329)
              ·
                refine ⟨40362793908362826262496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53817058544483768349995329 40362793908362826262496497)
                ·
                  refine ⟨30272095431272119696872373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40362793908362826262496497 30272095431272119696872373)
                  ·
                    refine ⟨2838008946681761221581785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30272095431272119696872373 2838008946681761221581785)
                    ·
                      refine ⟨2128506710011320916186339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838008946681761221581785 2128506710011320916186339)
                      ·
                        rfl

theorem cell23_4145252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_4145252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145252 prefixEnd_4145252 := by exact prefixLift 4145252
  have htrace : WordTrace (prefixWord ++ tailWord_4145252) baseStart_4145252 baseEnd_4145252 := by
    simpa [prefixWord, tailWord_4145252, baseEnd_4145252] using wordTrace_append hprefix tailTrace_4145252
  have hstable : (prefixWord ++ tailWord_4145252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145252).length < 2 ^ (prefixWord ++ tailWord_4145252).sum := by decide
  have hdescent : baseEnd_4145252 < baseStart_4145252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145262 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4145262 : Nat := 118140960795 + 4145262 * 2 ^ 59
def prefixEnd_4145262 : Nat := 4983230072969 + 3 ^ 40 * 4145262 * 2
def baseEnd_4145262 : Nat := 709503948272621959020431

theorem tailTrace_4145262 : CollatzResearch.WordTrace tailWord_4145262 prefixEnd_4145262 709503948272621959020431 := by
  unfold tailWord_4145262
  simp only [CollatzResearch.WordTrace]
  refine ⟨18898765738553900403947755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100793417272287468821054693 18898765738553900403947755)
  ·
    refine ⟨28348148607830850605921633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18898765738553900403947755 28348148607830850605921633)
    ·
      refine ⟨21261111455873137954441225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28348148607830850605921633 21261111455873137954441225)
      ·
        refine ⟨15945833591904853465830919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21261111455873137954441225 15945833591904853465830919)
        ·
          refine ⟨23918750387857280198746379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15945833591904853465830919 23918750387857280198746379)
          ·
            refine ⟨35878125581785920298119569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23918750387857280198746379 35878125581785920298119569)
            ·
              refine ⟨26908594186339440223589677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35878125581785920298119569 26908594186339440223589677)
              ·
                refine ⟨10090722819877290083846129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26908594186339440223589677 10090722819877290083846129)
                ·
                  refine ⟨7568042114907967562884597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10090722819877290083846129 7568042114907967562884597)
                  ·
                    refine ⟨709503948272621959020431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7568042114907967562884597 709503948272621959020431)
                    ·
                      rfl

theorem cell23_4145262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4145262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145262 prefixEnd_4145262 := by exact prefixLift 4145262
  have htrace : WordTrace (prefixWord ++ tailWord_4145262) baseStart_4145262 baseEnd_4145262 := by
    simpa [prefixWord, tailWord_4145262, baseEnd_4145262] using wordTrace_append hprefix tailTrace_4145262
  have hstable : (prefixWord ++ tailWord_4145262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145262).length < 2 ^ (prefixWord ++ tailWord_4145262).sum := by decide
  have hdescent : baseEnd_4145262 < baseStart_4145262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145265 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_4145265 : Nat := 118140960795 + 4145265 * 2 ^ 59
def prefixEnd_4145265 : Nat := 4983230072969 + 3 ^ 40 * 4145265 * 2
def baseEnd_4145265 : Nat := 2128513385259829365323779

theorem tailTrace_4145265 : CollatzResearch.WordTrace tailWord_4145265 prefixEnd_4145265 2128513385259829365323779 := by
  unfold tailWord_4145265
  simp only [CollatzResearch.WordTrace]
  refine ⟨151190235327420334743941249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100793490218280223162627499 151190235327420334743941249)
  ·
    refine ⟨113392676495565251057955937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151190235327420334743941249 113392676495565251057955937)
    ·
      refine ⟨85044507371673938293466953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113392676495565251057955937 85044507371673938293466953)
      ·
        refine ⟨63783380528755453720100215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85044507371673938293466953 63783380528755453720100215)
        ·
          refine ⟨95675070793133180580150323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63783380528755453720100215 95675070793133180580150323)
          ·
            refine ⟨143512606189699770870225485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95675070793133180580150323 143512606189699770870225485)
            ·
              refine ⟨53817227321137414076334557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143512606189699770870225485 53817227321137414076334557)
              ·
                refine ⟨20181460245426530278625459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53817227321137414076334557 20181460245426530278625459)
                ·
                  refine ⟨30272190368139795417938189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20181460245426530278625459 30272190368139795417938189)
                  ·
                    refine ⟨11352071388052423281726821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30272190368139795417938189 11352071388052423281726821)
                    ·
                      refine ⟨2128513385259829365323779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11352071388052423281726821 2128513385259829365323779)
                      ·
                        rfl

theorem cell23_4145265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_4145265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145265 prefixEnd_4145265 := by exact prefixLift 4145265
  have htrace : WordTrace (prefixWord ++ tailWord_4145265) baseStart_4145265 baseEnd_4145265 := by
    simpa [prefixWord, tailWord_4145265, baseEnd_4145265] using wordTrace_append hprefix tailTrace_4145265
  have hstable : (prefixWord ++ tailWord_4145265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145265).length < 2 ^ (prefixWord ++ tailWord_4145265).sum := by decide
  have hdescent : baseEnd_4145265 < baseStart_4145265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145383 : List Nat := [1, 1, 5, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4145383 : Nat := 118140960795 + 4145383 * 2 ^ 59
def prefixEnd_4145383 : Nat := 4983230072969 + 3 ^ 40 * 4145383 * 2
def baseEnd_4145383 : Nat := 2128573975977059903648237

theorem tailTrace_4145383 : CollatzResearch.WordTrace tailWord_4145383 prefixEnd_4145383 2128573975977059903648237 := by
  unfold tailWord_4145383
  simp only [CollatzResearch.WordTrace]
  refine ⟨151194539140992840896736803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100796359427328560597824535 151194539140992840896736803)
  ·
    refine ⟨226791808711489261345105205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151194539140992840896736803 226791808711489261345105205)
    ·
      refine ⟨21261732066702118251103613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226791808711489261345105205 21261732066702118251103613)
      ·
        refine ⟨7973149525013294344163855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21261732066702118251103613 7973149525013294344163855)
        ·
          refine ⟨11959724287519941516245783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7973149525013294344163855 11959724287519941516245783)
          ·
            refine ⟨17939586431279912274368675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959724287519941516245783 17939586431279912274368675)
            ·
              refine ⟨26909379646919868411553013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17939586431279912274368675 26909379646919868411553013)
              ·
                refine ⟨2522754341898737663583095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26909379646919868411553013 2522754341898737663583095)
                ·
                  refine ⟨3784131512848106495374643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522754341898737663583095 3784131512848106495374643)
                  ·
                    refine ⟨5676197269272159743061965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3784131512848106495374643 5676197269272159743061965)
                    ·
                      refine ⟨2128573975977059903648237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5676197269272159743061965 2128573975977059903648237)
                      ·
                        rfl

theorem cell23_4145383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4145383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145383 prefixEnd_4145383 := by exact prefixLift 4145383
  have htrace : WordTrace (prefixWord ++ tailWord_4145383) baseStart_4145383 baseEnd_4145383 := by
    simpa [prefixWord, tailWord_4145383, baseEnd_4145383] using wordTrace_append hprefix tailTrace_4145383
  have hstable : (prefixWord ++ tailWord_4145383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145383).length < 2 ^ (prefixWord ++ tailWord_4145383).sum := by decide
  have hdescent : baseEnd_4145383 < baseStart_4145383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145395 : List Nat := [1, 1, 1, 2, 2, 4, 12]
def baseStart_4145395 : Nat := 118140960795 + 4145395 * 2 ^ 59
def prefixEnd_4145395 : Nat := 4983230072969 + 3 ^ 40 * 4145395 * 2
def baseEnd_4145395 : Nat := 26278767132653257490101

theorem tailTrace_4145395 : CollatzResearch.WordTrace tailWord_4145395 prefixEnd_4145395 26278767132653257490101 := by
  unfold tailWord_4145395
  simp only [CollatzResearch.WordTrace]
  refine ⟨151194976816949366946173639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100796651211299577964115759 151194976816949366946173639)
  ·
    refine ⟨226792465225424050419260459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151194976816949366946173639 226792465225424050419260459)
    ·
      refine ⟨340188697838136075628890689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226792465225424050419260459 340188697838136075628890689)
      ·
        refine ⟨255141523378602056721668017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340188697838136075628890689 255141523378602056721668017)
        ·
          refine ⟨191356142533951542541251013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255141523378602056721668017 191356142533951542541251013)
          ·
            refine ⟨35879276725115914226484565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191356142533951542541251013 35879276725115914226484565)
            ·
              refine ⟨26278767132653257490101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 35879276725115914226484565 26278767132653257490101)
              ·
                rfl

theorem cell23_4145395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 12].length) (baseStart_4145395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145395 prefixEnd_4145395 := by exact prefixLift 4145395
  have htrace : WordTrace (prefixWord ++ tailWord_4145395) baseStart_4145395 baseEnd_4145395 := by
    simpa [prefixWord, tailWord_4145395, baseEnd_4145395] using wordTrace_append hprefix tailTrace_4145395
  have hstable : (prefixWord ++ tailWord_4145395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145395).length < 2 ^ (prefixWord ++ tailWord_4145395).sum := by decide
  have hdescent : baseEnd_4145395 < baseStart_4145395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145440 : List Nat := [2, 1, 1, 5, 2, 1, 3, 3, 1, 2, 2]
def baseStart_4145440 : Nat := 118140960795 + 4145440 * 2 ^ 59
def prefixEnd_4145440 : Nat := 4983230072969 + 3 ^ 40 * 4145440 * 2
def baseEnd_4145440 : Nat := 2128603244374366180635475

theorem tailTrace_4145440 : CollatzResearch.WordTrace tailWord_4145440 prefixEnd_4145440 2128603244374366180635475 := by
  unfold tailWord_4145440
  simp only [CollatzResearch.WordTrace]
  refine ⟨75598309050893169815780887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100797745401190893087707849 75598309050893169815780887)
  ·
    refine ⟨113397463576339754723671331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75598309050893169815780887 113397463576339754723671331)
    ·
      refine ⟨170096195364509632085506997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113397463576339754723671331 170096195364509632085506997)
      ·
        refine ⟨15946518315422778008016281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170096195364509632085506997 15946518315422778008016281)
        ·
          refine ⟨11959888736567083506012211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15946518315422778008016281 11959888736567083506012211)
          ·
            refine ⟨17939833104850625259018317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959888736567083506012211 17939833104850625259018317)
            ·
              refine ⟨6727437414318984472131869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17939833104850625259018317 6727437414318984472131869)
              ·
                refine ⟨2522789030369619177049451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6727437414318984472131869 2522789030369619177049451)
                ·
                  refine ⟨3784183545554428765574177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522789030369619177049451 3784183545554428765574177)
                  ·
                    refine ⟨2838137659165821574180633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3784183545554428765574177 2838137659165821574180633)
                    ·
                      refine ⟨2128603244374366180635475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838137659165821574180633 2128603244374366180635475)
                      ·
                        rfl

theorem cell23_4145440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_4145440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145440 prefixEnd_4145440 := by exact prefixLift 4145440
  have htrace : WordTrace (prefixWord ++ tailWord_4145440) baseStart_4145440 baseEnd_4145440 := by
    simpa [prefixWord, tailWord_4145440, baseEnd_4145440] using wordTrace_append hprefix tailTrace_4145440
  have hstable : (prefixWord ++ tailWord_4145440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145440).length < 2 ^ (prefixWord ++ tailWord_4145440).sum := by decide
  have hdescent : baseEnd_4145440 < baseStart_4145440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145457 : List Nat := [1, 2, 2, 3, 4, 1, 3, 2, 1, 2, 2]
def baseStart_4145457 : Nat := 118140960795 + 4145457 * 2 ^ 59
def prefixEnd_4145457 : Nat := 4983230072969 + 3 ^ 40 * 4145457 * 2
def baseEnd_4145457 : Nat := 2128611973545492614122897

theorem tailTrace_4145457 : CollatzResearch.WordTrace tailWord_4145457 prefixEnd_4145457 2128611973545492614122897 := by
  unfold tailWord_4145457
  simp only [CollatzResearch.WordTrace]
  refine ⟨151197238142724751534930625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100798158761816501023287083 151197238142724751534930625)
  ·
    refine ⟨113397928607043563651197969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151197238142724751534930625 113397928607043563651197969)
    ·
      refine ⟨85048446455282672738398477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113397928607043563651197969 85048446455282672738398477)
      ·
        refine ⟨31893167420731002276899429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85048446455282672738398477 31893167420731002276899429)
        ·
          refine ⟨5979968891387062926918643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31893167420731002276899429 5979968891387062926918643)
          ·
            refine ⟨8969953337080594390377965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5979968891387062926918643 8969953337080594390377965)
            ·
              refine ⟨3363732501405222896391737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8969953337080594390377965 3363732501405222896391737)
              ·
                refine ⟨2522799376053917172293803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3363732501405222896391737 2522799376053917172293803)
                ·
                  refine ⟨3784199064080875758440705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522799376053917172293803 3784199064080875758440705)
                  ·
                    refine ⟨2838149298060656818830529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3784199064080875758440705 2838149298060656818830529)
                    ·
                      refine ⟨2128611973545492614122897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838149298060656818830529 2128611973545492614122897)
                      ·
                        rfl

theorem cell23_4145457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_4145457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145457 prefixEnd_4145457 := by exact prefixLift 4145457
  have htrace : WordTrace (prefixWord ++ tailWord_4145457) baseStart_4145457 baseEnd_4145457 := by
    simpa [prefixWord, tailWord_4145457, baseEnd_4145457] using wordTrace_append hprefix tailTrace_4145457
  have hstable : (prefixWord ++ tailWord_4145457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145457).length < 2 ^ (prefixWord ++ tailWord_4145457).sum := by decide
  have hdescent : baseEnd_4145457 < baseStart_4145457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145496 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 4, 2, 2]
def baseStart_4145496 : Nat := 118140960795 + 4145496 * 2 ^ 59
def prefixEnd_4145496 : Nat := 4983230072969 + 3 ^ 40 * 4145496 * 2
def baseEnd_4145496 : Nat := 2128631999291017961535217

theorem tailTrace_4145496 : CollatzResearch.WordTrace tailWord_4145496 prefixEnd_4145496 2128631999291017961535217 := by
  unfold tailWord_4145496
  simp only [CollatzResearch.WordTrace]
  refine ⟨75599330294791730597800171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100799107059722307463733561 75599330294791730597800171)
  ·
    refine ⟨113398995442187595896700257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75599330294791730597800171 113398995442187595896700257)
    ·
      refine ⟨85049246581640696922525193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113398995442187595896700257 85049246581640696922525193)
      ·
        refine ⟨63786934936230522691893895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85049246581640696922525193 63786934936230522691893895)
        ·
          refine ⟨95680402404345784037840843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63786934936230522691893895 95680402404345784037840843)
          ·
            refine ⟨143520603606518676056761265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95680402404345784037840843 143520603606518676056761265)
            ·
              refine ⟨107640452704889007042570949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143520603606518676056761265 107640452704889007042570949)
              ·
                refine ⟨20182584882166688820482053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107640452704889007042570949 20182584882166688820482053)
                ·
                  refine ⟨3784234665406254153840385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20182584882166688820482053 3784234665406254153840385)
                  ·
                    refine ⟨2838175999054690615380289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3784234665406254153840385 2838175999054690615380289)
                    ·
                      refine ⟨2128631999291017961535217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838175999054690615380289 2128631999291017961535217)
                      ·
                        rfl

theorem cell23_4145496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_4145496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145496 prefixEnd_4145496 := by exact prefixLift 4145496
  have htrace : WordTrace (prefixWord ++ tailWord_4145496) baseStart_4145496 baseEnd_4145496 := by
    simpa [prefixWord, tailWord_4145496, baseEnd_4145496] using wordTrace_append hprefix tailTrace_4145496
  have hstable : (prefixWord ++ tailWord_4145496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145496).length < 2 ^ (prefixWord ++ tailWord_4145496).sum := by decide
  have hdescent : baseEnd_4145496 < baseStart_4145496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145513 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 2, 2, 2]
def baseStart_4145513 : Nat := 118140960795 + 4145513 * 2 ^ 59
def prefixEnd_4145513 : Nat := 4983230072969 + 3 ^ 40 * 4145513 * 2
def baseEnd_4145513 : Nat := 2128640728462144395022639

theorem tailTrace_4145513 : CollatzResearch.WordTrace tailWord_4145513 prefixEnd_4145513 2128640728462144395022639 := by
  unfold tailWord_4145513
  simp only [CollatzResearch.WordTrace]
  refine ⟨151199280630521873098969193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100799520420347915399312795 151199280630521873098969193)
  ·
    refine ⟨113399460472891404824226895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151199280630521873098969193 113399460472891404824226895)
    ·
      refine ⟨170099190709337107236340343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113399460472891404824226895 170099190709337107236340343)
      ·
        refine ⟨255148786064005660854510515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170099190709337107236340343 255148786064005660854510515)
        ·
          refine ⟨382723179096008491281765773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255148786064005660854510515 382723179096008491281765773)
          ·
            refine ⟨143521192161003184230662165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382723179096008491281765773 143521192161003184230662165)
            ·
              refine ⟨6727555882547024260812289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143521192161003184230662165 6727555882547024260812289)
              ·
                refine ⟨5045666911910268195609217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727555882547024260812289 5045666911910268195609217)
                ·
                  refine ⟨3784250183932701146706913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5045666911910268195609217 3784250183932701146706913)
                  ·
                    refine ⟨2838187637949525860030185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3784250183932701146706913 2838187637949525860030185)
                    ·
                      refine ⟨2128640728462144395022639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838187637949525860030185 2128640728462144395022639)
                      ·
                        rfl

theorem cell23_4145513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2, 2, 2].length) (baseStart_4145513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145513 prefixEnd_4145513 := by exact prefixLift 4145513
  have htrace : WordTrace (prefixWord ++ tailWord_4145513) baseStart_4145513 baseEnd_4145513 := by
    simpa [prefixWord, tailWord_4145513, baseEnd_4145513] using wordTrace_append hprefix tailTrace_4145513
  have hstable : (prefixWord ++ tailWord_4145513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145513).length < 2 ^ (prefixWord ++ tailWord_4145513).sum := by decide
  have hdescent : baseEnd_4145513 < baseStart_4145513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145586 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2]
def baseStart_4145586 : Nat := 118140960795 + 4145586 * 2 ^ 59
def prefixEnd_4145586 : Nat := 4983230072969 + 3 ^ 40 * 4145586 * 2
def baseEnd_4145586 : Nat := 2128678212549922609409803

theorem tailTrace_4145586 : CollatzResearch.WordTrace tailWord_4145586 prefixEnd_4145586 2128678212549922609409803 := by
  unfold tailWord_4145586
  simp only [CollatzResearch.WordTrace]
  refine ⟨37800485789814351641594153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100801295439504937710917741 37800485789814351641594153)
  ·
    refine ⟨28350364342360763731195615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37800485789814351641594153 28350364342360763731195615)
    ·
      refine ⟨42525546513541145596793423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28350364342360763731195615 42525546513541145596793423)
      ·
        refine ⟨63788319770311718395190135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42525546513541145596793423 63788319770311718395190135)
        ·
          refine ⟨95682479655467577592785203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63788319770311718395190135 95682479655467577592785203)
          ·
            refine ⟨143523719483201366389177805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95682479655467577592785203 143523719483201366389177805)
            ·
              refine ⟨53821394806200512395941677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143523719483201366389177805 53821394806200512395941677)
              ·
                refine ⟨20183023052325192148478129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53821394806200512395941677 20183023052325192148478129)
                ·
                  refine ⟨15137267289243894111358597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20183023052325192148478129 15137267289243894111358597)
                  ·
                    refine ⟨2838237616733230145879737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15137267289243894111358597 2838237616733230145879737)
                    ·
                      refine ⟨2128678212549922609409803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838237616733230145879737 2128678212549922609409803)
                      ·
                        rfl

theorem cell23_4145586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_4145586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145586 prefixEnd_4145586 := by exact prefixLift 4145586
  have htrace : WordTrace (prefixWord ++ tailWord_4145586) baseStart_4145586 baseEnd_4145586 := by
    simpa [prefixWord, tailWord_4145586, baseEnd_4145586] using wordTrace_append hprefix tailTrace_4145586
  have hstable : (prefixWord ++ tailWord_4145586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145586).length < 2 ^ (prefixWord ++ tailWord_4145586).sum := by decide
  have hdescent : baseEnd_4145586 < baseStart_4145586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145663 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 2, 3, 2]
def baseStart_4145663 : Nat := 118140960795 + 4145663 * 2 ^ 59
def prefixEnd_4145663 : Nat := 4983230072969 + 3 ^ 40 * 4145663 * 2
def baseEnd_4145663 : Nat := 2128717750560318808146949

theorem tailTrace_4145663 : CollatzResearch.WordTrace tailWord_4145663 prefixEnd_4145663 2128717750560318808146949 := by
  unfold tailWord_4145663
  simp only [CollatzResearch.WordTrace]
  refine ⟨151204751579978448716929643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100803167719985632477953095 151204751579978448716929643)
  ·
    refine ⟨226807127369967673075394465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151204751579978448716929643 226807127369967673075394465)
    ·
      refine ⟨170105345527475754806545849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226807127369967673075394465 170105345527475754806545849)
      ·
        refine ⟨127579009145606816104909387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170105345527475754806545849 127579009145606816104909387)
        ·
          refine ⟨191368513718410224157364081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127579009145606816104909387 191368513718410224157364081)
          ·
            refine ⟨143526385288807668118023061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191368513718410224157364081 143526385288807668118023061)
            ·
              refine ⟨6727799310412859443032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143526385288807668118023061 6727799310412859443032331)
              ·
                refine ⟨10091698965619289164548497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727799310412859443032331 10091698965619289164548497)
                ·
                  refine ⟨7568774224214466873411373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10091698965619289164548497 7568774224214466873411373)
                  ·
                    refine ⟨2838290334080425077529265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7568774224214466873411373 2838290334080425077529265)
                    ·
                      refine ⟨2128717750560318808146949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838290334080425077529265 2128717750560318808146949)
                      ·
                        rfl

theorem cell23_4145663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 2, 3, 2].length) (baseStart_4145663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145663 prefixEnd_4145663 := by exact prefixLift 4145663
  have htrace : WordTrace (prefixWord ++ tailWord_4145663) baseStart_4145663 baseEnd_4145663 := by
    simpa [prefixWord, tailWord_4145663, baseEnd_4145663] using wordTrace_append hprefix tailTrace_4145663
  have hstable : (prefixWord ++ tailWord_4145663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145663).length < 2 ^ (prefixWord ++ tailWord_4145663).sum := by decide
  have hdescent : baseEnd_4145663 < baseStart_4145663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145669 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_4145669 : Nat := 118140960795 + 4145669 * 2 ^ 59
def prefixEnd_4145669 : Nat := 4983230072969 + 3 ^ 40 * 4145669 * 2
def baseEnd_4145669 : Nat := 709573610481415261557307

theorem tailTrace_4145669 : CollatzResearch.WordTrace tailWord_4145669 prefixEnd_4145669 709573610481415261557307 := by
  unfold tailWord_4145669
  simp only [CollatzResearch.WordTrace]
  refine ⟨151204970417956711741648061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100803313611971141161098707 151204970417956711741648061)
  ·
    refine ⟨56701863906733766903118023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151204970417956711741648061 56701863906733766903118023)
    ·
      refine ⟨85052795860100650354677035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56701863906733766903118023 85052795860100650354677035)
      ·
        refine ⟨127579193790150975532015553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85052795860100650354677035 127579193790150975532015553)
        ·
          refine ⟨95684395342613231649011665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127579193790150975532015553 95684395342613231649011665)
          ·
            refine ⟨71763296506959923736758749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95684395342613231649011665 71763296506959923736758749)
            ·
              refine ⟨26911236190109971401284531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71763296506959923736758749 26911236190109971401284531)
              ·
                refine ⟨40366854285164957101926797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26911236190109971401284531 40366854285164957101926797)
                ·
                  refine ⟨15137570356936858913222549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40366854285164957101926797 15137570356936858913222549)
                  ·
                    refine ⟨709573610481415261557307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15137570356936858913222549 709573610481415261557307)
                    ·
                      rfl

theorem cell23_4145669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_4145669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145669 prefixEnd_4145669 := by exact prefixLift 4145669
  have htrace : WordTrace (prefixWord ++ tailWord_4145669) baseStart_4145669 baseEnd_4145669 := by
    simpa [prefixWord, tailWord_4145669, baseEnd_4145669] using wordTrace_append hprefix tailTrace_4145669
  have hstable : (prefixWord ++ tailWord_4145669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145669).length < 2 ^ (prefixWord ++ tailWord_4145669).sum := by decide
  have hdescent : baseEnd_4145669 < baseStart_4145669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145727 : List Nat := [1, 1, 2, 2, 3, 2, 4, 3, 1, 2, 2]
def baseStart_4145727 : Nat := 118140960795 + 4145727 * 2 ^ 59
def prefixEnd_4145727 : Nat := 4983230072969 + 3 ^ 40 * 4145727 * 2
def baseEnd_4145727 : Nat := 2128750613322206557746655

theorem tailTrace_4145727 : CollatzResearch.WordTrace tailWord_4145727 prefixEnd_4145727 2128750613322206557746655 := by
  unfold tailWord_4145727
  simp only [CollatzResearch.WordTrace]
  refine ⟨151207085851746587647259435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100804723901164391764839623 151207085851746587647259435)
  ·
    refine ⟨226810628777619881470889153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151207085851746587647259435 226810628777619881470889153)
    ·
      refine ⟨170107971583214911103166865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226810628777619881470889153 170107971583214911103166865)
      ·
        refine ⟨127580978687411183327375149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170107971583214911103166865 127580978687411183327375149)
        ·
          refine ⟨47842867007779193747765681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127580978687411183327375149 47842867007779193747765681)
          ·
            refine ⟨35882150255834395310824261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47842867007779193747765681 35882150255834395310824261)
            ·
              refine ⟨6727903172968949120779549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35882150255834395310824261 6727903172968949120779549)
              ·
                refine ⟨2522963689863355920292331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6727903172968949120779549 2522963689863355920292331)
                ·
                  refine ⟨3784445534795033880438497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2522963689863355920292331 3784445534795033880438497)
                  ·
                    refine ⟨2838334151096275410328873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3784445534795033880438497 2838334151096275410328873)
                    ·
                      refine ⟨2128750613322206557746655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838334151096275410328873 2128750613322206557746655)
                      ·
                        rfl

theorem cell23_4145727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 3, 1, 2, 2].length) (baseStart_4145727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145727 prefixEnd_4145727 := by exact prefixLift 4145727
  have htrace : WordTrace (prefixWord ++ tailWord_4145727) baseStart_4145727 baseEnd_4145727 := by
    simpa [prefixWord, tailWord_4145727, baseEnd_4145727] using wordTrace_append hprefix tailTrace_4145727
  have hstable : (prefixWord ++ tailWord_4145727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145727).length < 2 ^ (prefixWord ++ tailWord_4145727).sum := by decide
  have hdescent : baseEnd_4145727 < baseStart_4145727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145783 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 1, 4, 2]
def baseStart_4145783 : Nat := 118140960795 + 4145783 * 2 ^ 59
def prefixEnd_4145783 : Nat := 4983230072969 + 3 ^ 40 * 4145783 * 2
def baseEnd_4145783 : Nat := 2128779368238858338646397

theorem tailTrace_4145783 : CollatzResearch.WordTrace tailWord_4145783 prefixEnd_4145783 2128779368238858338646397 := by
  unfold tailWord_4145783
  simp only [CollatzResearch.WordTrace]
  refine ⟨151209128339543709211298003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100806085559695806140865335 151209128339543709211298003)
  ·
    refine ⟨226813692509315563816947005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151209128339543709211298003 226813692509315563816947005)
    ·
      refine ⟨85055134690993336431355127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226813692509315563816947005 85055134690993336431355127)
      ·
        refine ⟨127582702036490004647032691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85055134690993336431355127 127582702036490004647032691)
        ·
          refine ⟨191374053054735006970549037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127582702036490004647032691 191374053054735006970549037)
          ·
            refine ⟨71765269895525627613955889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191374053054735006970549037 71765269895525627613955889)
            ·
              refine ⟨53823952421644220710466917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71765269895525627613955889 53823952421644220710466917)
              ·
                refine ⟨10091991079058291383212547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53823952421644220710466917 10091991079058291383212547)
                ·
                  refine ⟨15137986618587437074818821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091991079058291383212547 15137986618587437074818821)
                  ·
                    refine ⟨2838372490985144451528529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15137986618587437074818821 2838372490985144451528529)
                    ·
                      refine ⟨2128779368238858338646397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838372490985144451528529 2128779368238858338646397)
                      ·
                        rfl

theorem cell23_4145783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 4, 2].length) (baseStart_4145783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145783 prefixEnd_4145783 := by exact prefixLift 4145783
  have htrace : WordTrace (prefixWord ++ tailWord_4145783) baseStart_4145783 baseEnd_4145783 := by
    simpa [prefixWord, tailWord_4145783, baseEnd_4145783] using wordTrace_append hprefix tailTrace_4145783
  have hstable : (prefixWord ++ tailWord_4145783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145783).length < 2 ^ (prefixWord ++ tailWord_4145783).sum := by decide
  have hdescent : baseEnd_4145783 < baseStart_4145783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145834 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4145834 : Nat := 118140960795 + 4145834 * 2 ^ 59
def prefixEnd_4145834 : Nat := 4983230072969 + 3 ^ 40 * 4145834 * 2
def baseEnd_4145834 : Nat := 2128805555752237639108663

theorem tailTrace_4145834 : CollatzResearch.WordTrace tailWord_4145834 prefixEnd_4145834 2128805555752237639108663 := by
  unfold tailWord_4145834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37802747115589736230351139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100807325641572629947603037 37802747115589736230351139)
  ·
    refine ⟨56704120673384604345526709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37802747115589736230351139 56704120673384604345526709)
    ·
      refine ⟨5316011313129806657393129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56704120673384604345526709 5316011313129806657393129)
      ·
        refine ⟨3987008484847354993044847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5316011313129806657393129 3987008484847354993044847)
        ·
          refine ⟨5980512727271032489567271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987008484847354993044847 5980512727271032489567271)
          ·
            refine ⟨8970769090906548734350907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980512727271032489567271 8970769090906548734350907)
            ·
              refine ⟨13456153636359823101526361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8970769090906548734350907 13456153636359823101526361)
              ·
                refine ⟨10092115227269867326144771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13456153636359823101526361 10092115227269867326144771)
                ·
                  refine ⟨15138172840904800989217157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092115227269867326144771 15138172840904800989217157)
                  ·
                    refine ⟨2838407407669650185478217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15138172840904800989217157 2838407407669650185478217)
                    ·
                      refine ⟨2128805555752237639108663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838407407669650185478217 2128805555752237639108663)
                      ·
                        rfl

theorem cell23_4145834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4145834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145834 prefixEnd_4145834 := by exact prefixLift 4145834
  have htrace : WordTrace (prefixWord ++ tailWord_4145834) baseStart_4145834 baseEnd_4145834 := by
    simpa [prefixWord, tailWord_4145834, baseEnd_4145834] using wordTrace_append hprefix tailTrace_4145834
  have hstable : (prefixWord ++ tailWord_4145834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145834).length < 2 ^ (prefixWord ++ tailWord_4145834).sum := by decide
  have hdescent : baseEnd_4145834 < baseStart_4145834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145853 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_4145853 : Nat := 118140960795 + 4145853 * 2 ^ 59
def prefixEnd_4145853 : Nat := 4983230072969 + 3 ^ 40 * 4145853 * 2
def baseEnd_4145853 : Nat := 709605103961557688257025

theorem tailTrace_4145853 : CollatzResearch.WordTrace tailWord_4145853 prefixEnd_4145853 709605103961557688257025 := by
  unfold tailWord_4145853
  simp only [CollatzResearch.WordTrace]
  refine ⟨151211681449290111166346213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100807787632860074110897475 151211681449290111166346213)
  ·
    refine ⟨28352190271741895843689915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151211681449290111166346213 28352190271741895843689915)
    ·
      refine ⟨42528285407612843765534873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28352190271741895843689915 42528285407612843765534873)
      ·
        refine ⟨31896214055709632824151155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42528285407612843765534873 31896214055709632824151155)
        ·
          refine ⟨47844321083564449236226733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31896214055709632824151155 47844321083564449236226733)
          ·
            refine ⟨17941620406336668463585025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47844321083564449236226733 17941620406336668463585025)
            ·
              refine ⟨13456215304752501347688769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17941620406336668463585025 13456215304752501347688769)
              ·
                refine ⟨10092161478564376010766577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13456215304752501347688769 10092161478564376010766577)
                ·
                  refine ⟨7569121108923282008074933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10092161478564376010766577 7569121108923282008074933)
                  ·
                    refine ⟨709605103961557688257025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7569121108923282008074933 709605103961557688257025)
                    ·
                      rfl

theorem cell23_4145853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_4145853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145853 prefixEnd_4145853 := by exact prefixLift 4145853
  have htrace : WordTrace (prefixWord ++ tailWord_4145853) baseStart_4145853 baseEnd_4145853 := by
    simpa [prefixWord, tailWord_4145853, baseEnd_4145853] using wordTrace_append hprefix tailTrace_4145853
  have hstable : (prefixWord ++ tailWord_4145853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145853).length < 2 ^ (prefixWord ++ tailWord_4145853).sum := by decide
  have hdescent : baseEnd_4145853 < baseStart_4145853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145860 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_4145860 : Nat := 118140960795 + 4145860 * 2 ^ 59
def prefixEnd_4145860 : Nat := 4983230072969 + 3 ^ 40 * 4145860 * 2
def baseEnd_4145860 : Nat := 2128818906249254537383543

theorem tailTrace_4145860 : CollatzResearch.WordTrace tailWord_4145860 prefixEnd_4145860 2128818906249254537383543 := by
  unfold tailWord_4145860
  simp only [CollatzResearch.WordTrace]
  refine ⟨75605968380132375680925517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100807957840176500907900689 75605968380132375680925517)
  ·
    refine ⟨28352238142549640880347069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75605968380132375680925517 28352238142549640880347069)
    ·
      refine ⟨10632089303456115330130151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28352238142549640880347069 10632089303456115330130151)
      ·
        refine ⟨15948133955184172995195227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632089303456115330130151 15948133955184172995195227)
        ·
          refine ⟨23922200932776259492792841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15948133955184172995195227 23922200932776259492792841)
          ·
            refine ⟨17941650699582194619594631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23922200932776259492792841 17941650699582194619594631)
            ·
              refine ⟨26912476049373291929391947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17941650699582194619594631 26912476049373291929391947)
              ·
                refine ⟨40368714074059937894087921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26912476049373291929391947 40368714074059937894087921)
                ·
                  refine ⟨30276535555544953420565941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40368714074059937894087921 30276535555544953420565941)
                  ·
                    refine ⟨2838425208332339383178057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30276535555544953420565941 2838425208332339383178057)
                    ·
                      refine ⟨2128818906249254537383543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838425208332339383178057 2128818906249254537383543)
                      ·
                        rfl

theorem cell23_4145860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_4145860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145860 prefixEnd_4145860 := by exact prefixLift 4145860
  have htrace : WordTrace (prefixWord ++ tailWord_4145860) baseStart_4145860 baseEnd_4145860 := by
    simpa [prefixWord, tailWord_4145860, baseEnd_4145860] using wordTrace_append hprefix tailTrace_4145860
  have hstable : (prefixWord ++ tailWord_4145860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145860).length < 2 ^ (prefixWord ++ tailWord_4145860).sum := by decide
  have hdescent : baseEnd_4145860 < baseStart_4145860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145910 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4145910 : Nat := 118140960795 + 4145910 * 2 ^ 59
def prefixEnd_4145910 : Nat := 4983230072969 + 3 ^ 40 * 4145910 * 2
def baseEnd_4145910 : Nat := 2128844580281979341758313

theorem tailTrace_4145910 : CollatzResearch.WordTrace tailWord_4145910 prefixEnd_4145910 2128844580281979341758313 := by
  unfold tailWord_4145910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450860025630225618823199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100809173606722406600780789 9450860025630225618823199)
  ·
    refine ⟨14176290038445338428234799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9450860025630225618823199 14176290038445338428234799)
    ·
      refine ⟨21264435057668007642352199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14176290038445338428234799 21264435057668007642352199)
      ·
        refine ⟨31896652586502011463528299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21264435057668007642352199 31896652586502011463528299)
        ·
          refine ⟨47844978879753017195292449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31896652586502011463528299 47844978879753017195292449)
          ·
            refine ⟨35883734159814762896469337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47844978879753017195292449 35883734159814762896469337)
            ·
              refine ⟨26912800619861072172352003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35883734159814762896469337 26912800619861072172352003)
              ·
                refine ⟨40369200929791608258528005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26912800619861072172352003 40369200929791608258528005)
                ·
                  refine ⟨7569225174335926548474001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40369200929791608258528005 7569225174335926548474001)
                  ·
                    refine ⟨5676918880751944911355501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7569225174335926548474001 5676918880751944911355501)
                    ·
                      refine ⟨2128844580281979341758313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5676918880751944911355501 2128844580281979341758313)
                      ·
                        rfl

theorem cell23_4145910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4145910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145910 prefixEnd_4145910 := by exact prefixLift 4145910
  have htrace : WordTrace (prefixWord ++ tailWord_4145910) baseStart_4145910 baseEnd_4145910 := by
    simpa [prefixWord, tailWord_4145910, baseEnd_4145910] using wordTrace_append hprefix tailTrace_4145910
  have hstable : (prefixWord ++ tailWord_4145910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145910).length < 2 ^ (prefixWord ++ tailWord_4145910).sum := by decide
  have hdescent : baseEnd_4145910 < baseStart_4145910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145930 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_4145930 : Nat := 118140960795 + 4145930 * 2 ^ 59
def prefixEnd_4145930 : Nat := 4983230072969 + 3 ^ 40 * 4145930 * 2
def baseEnd_4145930 : Nat := 236539427766118807056469

theorem tailTrace_4145930 : CollatzResearch.WordTrace tailWord_4145930 prefixEnd_4145930 236539427766118807056469 := by
  unfold tailWord_4145930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37803622467502788329224811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100809659913340768877932829 37803622467502788329224811)
  ·
    refine ⟨56705433701254182493837217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37803622467502788329224811 56705433701254182493837217)
    ·
      refine ⟨42529075275940636870377913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56705433701254182493837217 42529075275940636870377913)
      ·
        refine ⟨31896806456955477652783435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42529075275940636870377913 31896806456955477652783435)
        ·
          refine ⟨47845209685433216479175153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31896806456955477652783435 47845209685433216479175153)
          ·
            refine ⟨35883907264074912359381365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47845209685433216479175153 35883907264074912359381365)
            ·
              refine ⟨3364116306007023033692003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35883907264074912359381365 3364116306007023033692003)
              ·
                refine ⟨5046174459010534550538005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364116306007023033692003 5046174459010534550538005)
                ·
                  refine ⟨236539427766118807056469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5046174459010534550538005 236539427766118807056469)
                  ·
                    rfl

theorem cell23_4145930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_4145930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145930 prefixEnd_4145930 := by exact prefixLift 4145930
  have htrace : WordTrace (prefixWord ++ tailWord_4145930) baseStart_4145930 baseEnd_4145930 := by
    simpa [prefixWord, tailWord_4145930, baseEnd_4145930] using wordTrace_append hprefix tailTrace_4145930
  have hstable : (prefixWord ++ tailWord_4145930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145930).length < 2 ^ (prefixWord ++ tailWord_4145930).sum := by decide
  have hdescent : baseEnd_4145930 < baseStart_4145930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145960 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4145960 : Nat := 118140960795 + 4145960 * 2 ^ 59
def prefixEnd_4145960 : Nat := 4983230072969 + 3 ^ 40 * 4145960 * 2
def baseEnd_4145960 : Nat := 709623418104901382044361

theorem tailTrace_4145960 : CollatzResearch.WordTrace tailWord_4145960 prefixEnd_4145960 709623418104901382044361 := by
  unfold tailWord_4145960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75607792029951234220245667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100810389373268312293660889 75607792029951234220245667)
  ·
    refine ⟨113411688044926851330368501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75607792029951234220245667 113411688044926851330368501)
    ·
      refine ⟨10632345754211892312222047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113411688044926851330368501 10632345754211892312222047)
      ·
        refine ⟨15948518631317838468333071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10632345754211892312222047 15948518631317838468333071)
        ·
          refine ⟨23922777946976757702499607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15948518631317838468333071 23922777946976757702499607)
          ·
            refine ⟨35884166920465136553749411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23922777946976757702499607 35884166920465136553749411)
            ·
              refine ⟨53826250380697704830624117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35884166920465136553749411 53826250380697704830624117)
              ·
                refine ⟨5046210973190409827871011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53826250380697704830624117 5046210973190409827871011)
                ·
                  refine ⟨7569316459785614741806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046210973190409827871011 7569316459785614741806517)
                  ·
                    refine ⟨709623418104901382044361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7569316459785614741806517 709623418104901382044361)
                    ·
                      rfl

theorem cell23_4145960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4145960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145960 prefixEnd_4145960 := by exact prefixLift 4145960
  have htrace : WordTrace (prefixWord ++ tailWord_4145960) baseStart_4145960 baseEnd_4145960 := by
    simpa [prefixWord, tailWord_4145960, baseEnd_4145960] using wordTrace_append hprefix tailTrace_4145960
  have hstable : (prefixWord ++ tailWord_4145960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145960).length < 2 ^ (prefixWord ++ tailWord_4145960).sum := by decide
  have hdescent : baseEnd_4145960 < baseStart_4145960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4145993 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_4145993 : Nat := 118140960795 + 4145993 * 2 ^ 59
def prefixEnd_4145993 : Nat := 4983230072969 + 3 ^ 40 * 4145993 * 2
def baseEnd_4145993 : Nat := 2128887199176302517020431

theorem tailTrace_4145993 : CollatzResearch.WordTrace tailWord_4145993 prefixEnd_4145993 2128887199176302517020431 := by
  unfold tailWord_4145993
  simp only [CollatzResearch.WordTrace]
  refine ⟨151216787668782915076442633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100811191779188610050961755 151216787668782915076442633)
  ·
    refine ⟨113412590751587186307331975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151216787668782915076442633 113412590751587186307331975)
    ·
      refine ⟨170118886127380779460997963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113412590751587186307331975 170118886127380779460997963)
      ·
        refine ⟨255178329191071169191496945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170118886127380779460997963 255178329191071169191496945)
        ·
          refine ⟨191383746893303376893622709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255178329191071169191496945 191383746893303376893622709)
          ·
            refine ⟨17942226271247191583777129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191383746893303376893622709 17942226271247191583777129)
            ·
              refine ⟨13456669703435393687832847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17942226271247191583777129 13456669703435393687832847)
              ·
                refine ⟨20185004555153090531749271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13456669703435393687832847 20185004555153090531749271)
                ·
                  refine ⟨30277506832729635797623907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20185004555153090531749271 30277506832729635797623907)
                  ·
                    refine ⟨45416260249094453696435861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30277506832729635797623907 45416260249094453696435861)
                    ·
                      refine ⟨2128887199176302517020431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45416260249094453696435861 2128887199176302517020431)
                      ·
                        rfl

theorem cell23_4145993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_4145993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4145993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4145993 prefixEnd_4145993 := by exact prefixLift 4145993
  have htrace : WordTrace (prefixWord ++ tailWord_4145993) baseStart_4145993 baseEnd_4145993 := by
    simpa [prefixWord, tailWord_4145993, baseEnd_4145993] using wordTrace_append hprefix tailTrace_4145993
  have hstable : (prefixWord ++ tailWord_4145993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4145993).length < 2 ^ (prefixWord ++ tailWord_4145993).sum := by decide
  have hdescent : baseEnd_4145993 < baseStart_4145993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4145993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146010 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_4146010 : Nat := 118140960795 + 4146010 * 2 ^ 59
def prefixEnd_4146010 : Nat := 4983230072969 + 3 ^ 40 * 4146010 * 2
def baseEnd_4146010 : Nat := 2128895928347428950507853

theorem tailTrace_4146010 : CollatzResearch.WordTrace tailWord_4146010 prefixEnd_4146010 2128895928347428950507853 := by
  unfold tailWord_4146010
  simp only [CollatzResearch.WordTrace]
  refine ⟨37804351927430331744952871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100811605139814217986540989 37804351927430331744952871)
  ·
    refine ⟨56706527891145497617429307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37804351927430331744952871 56706527891145497617429307)
    ·
      refine ⟨85059791836718246426143961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56706527891145497617429307 85059791836718246426143961)
      ·
        refine ⟨63794843877538684819607971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85059791836718246426143961 63794843877538684819607971)
        ·
          refine ⟨95692265816308027229411957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63794843877538684819607971 95692265816308027229411957)
          ·
            refine ⟨8971149920278877552757371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95692265816308027229411957 8971149920278877552757371)
            ·
              refine ⟨13456724880418316329136057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971149920278877552757371 13456724880418316329136057)
              ·
                refine ⟨10092543660313737246852043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13456724880418316329136057 10092543660313737246852043)
                ·
                  refine ⟨15138815490470605870278065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092543660313737246852043 15138815490470605870278065)
                  ·
                    refine ⟨11354111617852954402708549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15138815490470605870278065 11354111617852954402708549)
                    ·
                      refine ⟨2128895928347428950507853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11354111617852954402708549 2128895928347428950507853)
                      ·
                        rfl

theorem cell23_4146010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_4146010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146010 prefixEnd_4146010 := by exact prefixLift 4146010
  have htrace : WordTrace (prefixWord ++ tailWord_4146010) baseStart_4146010 baseEnd_4146010 := by
    simpa [prefixWord, tailWord_4146010, baseEnd_4146010] using wordTrace_append hprefix tailTrace_4146010
  have hstable : (prefixWord ++ tailWord_4146010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146010).length < 2 ^ (prefixWord ++ tailWord_4146010).sum := by decide
  have hdescent : baseEnd_4146010 < baseStart_4146010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146033 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 2, 7]
def baseStart_4146033 : Nat := 118140960795 + 4146033 * 2 ^ 59
def prefixEnd_4146033 : Nat := 4983230072969 + 3 ^ 40 * 4146033 * 2
def baseEnd_4146033 : Nat := 709635912800827453506749

theorem tailTrace_4146033 : CollatzResearch.WordTrace tailWord_4146033 prefixEnd_4146033 709635912800827453506749 := by
  unfold tailWord_4146033
  simp only [CollatzResearch.WordTrace]
  refine ⟨151218246588638001907898753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100812164392425334605265835 151218246588638001907898753)
  ·
    refine ⟨113413684941478501430924065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151218246588638001907898753 113413684941478501430924065)
    ·
      refine ⟨85060263706108876073193049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113413684941478501430924065 85060263706108876073193049)
      ·
        refine ⟨63795197779581657054894787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85060263706108876073193049 63795197779581657054894787)
        ·
          refine ⟨95692796669372485582342181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63795197779581657054894787 95692796669372485582342181)
          ·
            refine ⟨17942399375507341046689159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95692796669372485582342181 17942399375507341046689159)
            ·
              refine ⟨26913599063261011570033739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17942399375507341046689159 26913599063261011570033739)
              ·
                refine ⟨40370398594891517355050609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26913599063261011570033739 40370398594891517355050609)
                ·
                  refine ⟨30277798946168638016287957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40370398594891517355050609 30277798946168638016287957)
                  ·
                    refine ⟨709635912800827453506749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30277798946168638016287957 709635912800827453506749)
                    ·
                      rfl

theorem cell23_4146033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_4146033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146033 prefixEnd_4146033 := by exact prefixLift 4146033
  have htrace : WordTrace (prefixWord ++ tailWord_4146033) baseStart_4146033 baseEnd_4146033 := by
    simpa [prefixWord, tailWord_4146033, baseEnd_4146033] using wordTrace_append hprefix tailTrace_4146033
  have hstable : (prefixWord ++ tailWord_4146033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146033).length < 2 ^ (prefixWord ++ tailWord_4146033).sum := by decide
  have hdescent : baseEnd_4146033 < baseStart_4146033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146047 : List Nat := [1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 3]
def baseStart_4146047 : Nat := 118140960795 + 4146047 * 2 ^ 59
def prefixEnd_4146047 : Nat := 4983230072969 + 3 ^ 40 * 4146047 * 2
def baseEnd_4146047 : Nat := 2128914927131645305745183

theorem tailTrace_4146047 : CollatzResearch.WordTrace tailWord_4146047 prefixEnd_4146047 2128914927131645305745183 := by
  unfold tailWord_4146047
  simp only [CollatzResearch.WordTrace]
  refine ⟨151218757210587282298908395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100812504807058188199272263 151218757210587282298908395)
  ·
    refine ⟨226828135815880923448362593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151218757210587282298908395 226828135815880923448362593)
    ·
      refine ⟨170121101861910692586271945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226828135815880923448362593 170121101861910692586271945)
      ·
        refine ⟨127590826396433019439703959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170121101861910692586271945 127590826396433019439703959)
        ·
          refine ⟨191386239594649529159555939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127590826396433019439703959 191386239594649529159555939)
          ·
            refine ⟨287079359391974293739333909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191386239594649529159555939 287079359391974293739333909)
            ·
              refine ⟨13456844971498795019031277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287079359391974293739333909 13456844971498795019031277)
              ·
                refine ⟨5046316864312048132136729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13456844971498795019031277 5046316864312048132136729)
                ·
                  refine ⟨3784737648234036099102547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5046316864312048132136729 3784737648234036099102547)
                  ·
                    refine ⟨5677106472351054148653821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3784737648234036099102547 5677106472351054148653821)
                    ·
                      refine ⟨2128914927131645305745183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5677106472351054148653821 2128914927131645305745183)
                      ·
                        rfl

theorem cell23_4146047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_4146047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146047 prefixEnd_4146047 := by exact prefixLift 4146047
  have htrace : WordTrace (prefixWord ++ tailWord_4146047) baseStart_4146047 baseEnd_4146047 := by
    simpa [prefixWord, tailWord_4146047, baseEnd_4146047] using wordTrace_append hprefix tailTrace_4146047
  have hstable : (prefixWord ++ tailWord_4146047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146047).length < 2 ^ (prefixWord ++ tailWord_4146047).sum := by decide
  have hdescent : baseEnd_4146047 < baseStart_4146047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146057 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 3, 3, 2]
def baseStart_4146057 : Nat := 118140960795 + 4146057 * 2 ^ 59
def prefixEnd_4146057 : Nat := 4983230072969 + 3 ^ 40 * 4146057 * 2
def baseEnd_4146057 : Nat := 2128920061938190266620137

theorem tailTrace_4146057 : CollatzResearch.WordTrace tailWord_4146057 prefixEnd_4146057 2128920061938190266620137 := by
  unfold tailWord_4146057
  simp only [CollatzResearch.WordTrace]
  refine ⟨151219121940551054006772425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100812747960367369337848283 151219121940551054006772425)
  ·
    refine ⟨113414341455413290505079319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151219121940551054006772425 113414341455413290505079319)
    ·
      refine ⟨170121512183119935757618979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113414341455413290505079319 170121512183119935757618979)
      ·
        refine ⟨255182268274679903636428469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170121512183119935757618979 255182268274679903636428469)
        ·
          refine ⟨23923337650751240965915169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255182268274679903636428469 23923337650751240965915169)
          ·
            refine ⟨17942503238063430724436377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23923337650751240965915169 17942503238063430724436377)
            ·
              refine ⟨13456877428547573043327283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17942503238063430724436377 13456877428547573043327283)
              ·
                refine ⟨20185316142821359564990925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13456877428547573043327283 20185316142821359564990925)
                ·
                  refine ⟨7569493553558009836871597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20185316142821359564990925 7569493553558009836871597)
                  ·
                    refine ⟨2838560082584253688826849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7569493553558009836871597 2838560082584253688826849)
                    ·
                      refine ⟨2128920061938190266620137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838560082584253688826849 2128920061938190266620137)
                      ·
                        rfl

theorem cell23_4146057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 3, 3, 2].length) (baseStart_4146057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146057 prefixEnd_4146057 := by exact prefixLift 4146057
  have htrace : WordTrace (prefixWord ++ tailWord_4146057) baseStart_4146057 baseEnd_4146057 := by
    simpa [prefixWord, tailWord_4146057, baseEnd_4146057] using wordTrace_append hprefix tailTrace_4146057
  have hstable : (prefixWord ++ tailWord_4146057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146057).length < 2 ^ (prefixWord ++ tailWord_4146057).sum := by decide
  have hdescent : baseEnd_4146057 < baseStart_4146057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146073 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_4146073 : Nat := 118140960795 + 4146073 * 2 ^ 59
def prefixEnd_4146073 : Nat := 4983230072969 + 3 ^ 40 * 4146073 * 2
def baseEnd_4146073 : Nat := 2128928277628662204020063

theorem tailTrace_4146073 : CollatzResearch.WordTrace tailWord_4146073 prefixEnd_4146073 2128928277628662204020063 := by
  unfold tailWord_4146073
  simp only [CollatzResearch.WordTrace]
  refine ⟨151219705508493088739354873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100813137005662059159569915 151219705508493088739354873)
  ·
    refine ⟨113414779131369816554516155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151219705508493088739354873 113414779131369816554516155)
    ·
      refine ⟨170122168697054724831774233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113414779131369816554516155 170122168697054724831774233)
      ·
        refine ⟨127591626522791043623830675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170122168697054724831774233 127591626522791043623830675)
        ·
          refine ⟨191387439784186565435746013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127591626522791043623830675 191387439784186565435746013)
          ·
            refine ⟨71770289919069962038404755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191387439784186565435746013 71770289919069962038404755)
            ·
              refine ⟨107655434878604943057607133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71770289919069962038404755 107655434878604943057607133)
              ·
                refine ⟨40370788079476853646602675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107655434878604943057607133 40370788079476853646602675)
                ·
                  refine ⟨60556182119215280469904013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40370788079476853646602675 60556182119215280469904013)
                  ·
                    refine ⟨22708568294705730176214005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60556182119215280469904013 22708568294705730176214005)
                    ·
                      refine ⟨2128928277628662204020063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22708568294705730176214005 2128928277628662204020063)
                      ·
                        rfl

theorem cell23_4146073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_4146073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146073 prefixEnd_4146073 := by exact prefixLift 4146073
  have htrace : WordTrace (prefixWord ++ tailWord_4146073) baseStart_4146073 baseEnd_4146073 := by
    simpa [prefixWord, tailWord_4146073, baseEnd_4146073] using wordTrace_append hprefix tailTrace_4146073
  have hstable : (prefixWord ++ tailWord_4146073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146073).length < 2 ^ (prefixWord ++ tailWord_4146073).sum := by decide
  have hdescent : baseEnd_4146073 < baseStart_4146073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146081 : List Nat := [1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_4146081 : Nat := 118140960795 + 4146081 * 2 ^ 59
def prefixEnd_4146081 : Nat := 4983230072969 + 3 ^ 40 * 4146081 * 2
def baseEnd_4146081 : Nat := 2128932385473898172720027

theorem tailTrace_4146081 : CollatzResearch.WordTrace tailWord_4146081 prefixEnd_4146081 2128932385473898172720027 := by
  unfold tailWord_4146081
  simp only [CollatzResearch.WordTrace]
  refine ⟨151219997292464106105646097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100813331528309404070430731 151219997292464106105646097)
  ·
    refine ⟨113414997969348079579234573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151219997292464106105646097 113414997969348079579234573)
    ·
      refine ⟨42530624238505529842212965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113414997969348079579234573 42530624238505529842212965)
      ·
        refine ⟨7974492044719786845414931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42530624238505529842212965 7974492044719786845414931)
        ·
          refine ⟨11961738067079680268122397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974492044719786845414931 11961738067079680268122397)
          ·
            refine ⟨4485651775154880100545899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11961738067079680268122397 4485651775154880100545899)
            ·
              refine ⟨6728477662732320150818849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485651775154880100545899 6728477662732320150818849)
              ·
                refine ⟨5046358247049240113114137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728477662732320150818849 5046358247049240113114137)
                ·
                  refine ⟨3784768685286930084835603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5046358247049240113114137 3784768685286930084835603)
                  ·
                    refine ⟨5677153027930395127253405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3784768685286930084835603 5677153027930395127253405)
                    ·
                      refine ⟨2128932385473898172720027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5677153027930395127253405 2128932385473898172720027)
                      ·
                        rfl

theorem cell23_4146081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_4146081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146081 prefixEnd_4146081 := by exact prefixLift 4146081
  have htrace : WordTrace (prefixWord ++ tailWord_4146081) baseStart_4146081 baseEnd_4146081 := by
    simpa [prefixWord, tailWord_4146081, baseEnd_4146081] using wordTrace_append hprefix tailTrace_4146081
  have hstable : (prefixWord ++ tailWord_4146081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146081).length < 2 ^ (prefixWord ++ tailWord_4146081).sum := by decide
  have hdescent : baseEnd_4146081 < baseStart_4146081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146104 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 1, 4, 2]
def baseStart_4146104 : Nat := 118140960795 + 4146104 * 2 ^ 59
def prefixEnd_4146104 : Nat := 4983230072969 + 3 ^ 40 * 4146104 * 2
def baseEnd_4146104 : Nat := 2128944195528951582732421

theorem tailTrace_4146104 : CollatzResearch.WordTrace tailWord_4146104 prefixEnd_4146104 2128944195528951582732421 := by
  unfold tailWord_4146104
  simp only [CollatzResearch.WordTrace]
  refine ⟨75610418085690390516866683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100813890780920520689155577 75610418085690390516866683)
  ·
    refine ⟨113415627128535585775300025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75610418085690390516866683 113415627128535585775300025)
    ·
      refine ⟨85061720346401689331475019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113415627128535585775300025 85061720346401689331475019)
      ·
        refine ⟨127592580519602533997212529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85061720346401689331475019 127592580519602533997212529)
        ·
          refine ⟨95694435389701900497909397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127592580519602533997212529 95694435389701900497909397)
          ·
            refine ⟨4485676658892276585839503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95694435389701900497909397 4485676658892276585839503)
            ·
              refine ⟨6728514988338414878759255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4485676658892276585839503 6728514988338414878759255)
              ·
                refine ⟨10092772482507622318138883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728514988338414878759255 10092772482507622318138883)
                ·
                  refine ⟨15139158723761433477208325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092772482507622318138883 15139158723761433477208325)
                  ·
                    refine ⟨2838592260705268776976561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15139158723761433477208325 2838592260705268776976561)
                    ·
                      refine ⟨2128944195528951582732421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838592260705268776976561 2128944195528951582732421)
                      ·
                        rfl

theorem cell23_4146104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 1, 4, 2].length) (baseStart_4146104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146104 prefixEnd_4146104 := by exact prefixLift 4146104
  have htrace : WordTrace (prefixWord ++ tailWord_4146104) baseStart_4146104 baseEnd_4146104 := by
    simpa [prefixWord, tailWord_4146104, baseEnd_4146104] using wordTrace_append hprefix tailTrace_4146104
  have hstable : (prefixWord ++ tailWord_4146104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146104).length < 2 ^ (prefixWord ++ tailWord_4146104).sum := by decide
  have hdescent : baseEnd_4146104 < baseStart_4146104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146110 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_4146110 : Nat := 118140960795 + 4146110 * 2 ^ 59
def prefixEnd_4146110 : Nat := 4983230072969 + 3 ^ 40 * 4146110 * 2
def baseEnd_4146110 : Nat := 236549697379208728806377

theorem tailTrace_4146110 : CollatzResearch.WordTrace tailWord_4146110 prefixEnd_4146110 236549697379208728806377 := by
  unfold tailWord_4146110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18902631876169880507306473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100814036672906029372301189 18902631876169880507306473)
  ·
    refine ⟨14176973907127410380479855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18902631876169880507306473 14176973907127410380479855)
    ·
      refine ⟨21265460860691115570719783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14176973907127410380479855 21265460860691115570719783)
      ·
        refine ⟨31898191291036673356079675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21265460860691115570719783 31898191291036673356079675)
        ·
          refine ⟨47847286936555010034119513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31898191291036673356079675 47847286936555010034119513)
          ·
            refine ⟨35885465202416257525589635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47847286936555010034119513 35885465202416257525589635)
            ·
              refine ⟨53828197803624386288384453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35885465202416257525589635 53828197803624386288384453)
              ·
                refine ⟨10092787088179572429072085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53828197803624386288384453 10092787088179572429072085)
                ·
                  refine ⟨236549697379208728806377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10092787088179572429072085 236549697379208728806377)
                  ·
                    rfl

theorem cell23_4146110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_4146110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146110 prefixEnd_4146110 := by exact prefixLift 4146110
  have htrace : WordTrace (prefixWord ++ tailWord_4146110) baseStart_4146110 baseEnd_4146110 := by
    simpa [prefixWord, tailWord_4146110, baseEnd_4146110] using wordTrace_append hprefix tailTrace_4146110
  have hstable : (prefixWord ++ tailWord_4146110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146110).length < 2 ^ (prefixWord ++ tailWord_4146110).sum := by decide
  have hdescent : baseEnd_4146110 < baseStart_4146110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146127 : List Nat := [1, 1, 2, 1, 1, 6, 3, 3, 5]
def baseStart_4146127 : Nat := 118140960795 + 4146127 * 2 ^ 59
def prefixEnd_4146127 : Nat := 4983230072969 + 3 ^ 40 * 4146127 * 2
def baseEnd_4146127 : Nat := 236550667287111665860535

theorem tailTrace_4146127 : CollatzResearch.WordTrace tailWord_4146127 prefixEnd_4146127 236550667287111665860535 := by
  unfold tailWord_4146127
  simp only [CollatzResearch.WordTrace]
  refine ⟨151221675050297455961820635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100814450033531637307880423 151221675050297455961820635)
  ·
    refine ⟨226832512575446183942730953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151221675050297455961820635 226832512575446183942730953)
    ·
      refine ⟨170124384431584637957048215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226832512575446183942730953 170124384431584637957048215)
      ·
        refine ⟨255186576647376956935572323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170124384431584637957048215 255186576647376956935572323)
        ·
          refine ⟨382779864971065435403358485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255186576647376956935572323 382779864971065435403358485)
          ·
            refine ⟨17942806170518692284532429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382779864971065435403358485 17942806170518692284532429)
            ·
              refine ⟨6728552313944509606699661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17942806170518692284532429 6728552313944509606699661)
              ·
                refine ⟨2523207117729191102512373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6728552313944509606699661 2523207117729191102512373)
                ·
                  refine ⟨236550667287111665860535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2523207117729191102512373 236550667287111665860535)
                  ·
                    rfl

theorem cell23_4146127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 3, 5].length) (baseStart_4146127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146127 prefixEnd_4146127 := by exact prefixLift 4146127
  have htrace : WordTrace (prefixWord ++ tailWord_4146127) baseStart_4146127 baseEnd_4146127 := by
    simpa [prefixWord, tailWord_4146127, baseEnd_4146127] using wordTrace_append hprefix tailTrace_4146127
  have hstable : (prefixWord ++ tailWord_4146127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146127).length < 2 ^ (prefixWord ++ tailWord_4146127).sum := by decide
  have hdescent : baseEnd_4146127 < baseStart_4146127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146147 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 2, 5, 2]
def baseStart_4146147 : Nat := 118140960795 + 4146147 * 2 ^ 59
def prefixEnd_4146147 : Nat := 4983230072969 + 3 ^ 40 * 4146147 * 2
def baseEnd_4146147 : Nat := 2128966275197094914494723

theorem tailTrace_4146147 : CollatzResearch.WordTrace tailWord_4146147 prefixEnd_4146147 2128966275197094914494723 := by
  unfold tailWord_4146147
  simp only [CollatzResearch.WordTrace]
  refine ⟨151222404510224999377548695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100814936340149999585032463 151222404510224999377548695)
  ·
    refine ⟨226833606765337499066323043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151222404510224999377548695 226833606765337499066323043)
    ·
      refine ⟨340250410148006248599484565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226833606765337499066323043 340250410148006248599484565)
      ·
        refine ⟨15949237975687792903100839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 340250410148006248599484565 15949237975687792903100839)
        ·
          refine ⟨23923856963531689354651259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15949237975687792903100839 23923856963531689354651259)
          ·
            refine ⟨35885785445297534031976889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23923856963531689354651259 35885785445297534031976889)
            ·
              refine ⟨26914339083973150523982667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35885785445297534031976889 26914339083973150523982667)
              ·
                refine ⟨40371508625959725785974001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26914339083973150523982667 40371508625959725785974001)
                ·
                  refine ⟨30278631469469794339480501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40371508625959725785974001 30278631469469794339480501)
                  ·
                    refine ⟨2838621700262793219326297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30278631469469794339480501 2838621700262793219326297)
                    ·
                      refine ⟨2128966275197094914494723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838621700262793219326297 2128966275197094914494723)
                      ·
                        rfl

theorem cell23_4146147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_4146147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146147 prefixEnd_4146147 := by exact prefixLift 4146147
  have htrace : WordTrace (prefixWord ++ tailWord_4146147) baseStart_4146147 baseEnd_4146147 := by
    simpa [prefixWord, tailWord_4146147, baseEnd_4146147] using wordTrace_append hprefix tailTrace_4146147
  have hstable : (prefixWord ++ tailWord_4146147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146147).length < 2 ^ (prefixWord ++ tailWord_4146147).sum := by decide
  have hdescent : baseEnd_4146147 < baseStart_4146147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146160 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4]
def baseStart_4146160 : Nat := 118140960795 + 4146160 * 2 ^ 59
def prefixEnd_4146160 : Nat := 4983230072969 + 3 ^ 40 * 4146160 * 2
def baseEnd_4146160 : Nat := 2128972950445603363632163

theorem tailTrace_4146160 : CollatzResearch.WordTrace tailWord_4146160 prefixEnd_4146160 2128972950445603363632163 := by
  unfold tailWord_4146160
  simp only [CollatzResearch.WordTrace]
  refine ⟨75611439329588951298885967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100815252439451935065181289 75611439329588951298885967)
  ·
    refine ⟨113417158994383426948328951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75611439329588951298885967 113417158994383426948328951)
    ·
      refine ⟨170125738491575140422493427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113417158994383426948328951 170125738491575140422493427)
      ·
        refine ⟨255188607737362710633740141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170125738491575140422493427 255188607737362710633740141)
        ·
          refine ⟨95695727901511016487652553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255188607737362710633740141 95695727901511016487652553)
          ·
            refine ⟨71771795926133262365739415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95695727901511016487652553 71771795926133262365739415)
            ·
              refine ⟨107657693889199893548609123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71771795926133262365739415 107657693889199893548609123)
              ·
                refine ⟨161486540833799840322913685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107657693889199893548609123 161486540833799840322913685)
                ·
                  refine ⟨7569681601584367515136579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161486540833799840322913685 7569681601584367515136579)
                  ·
                    refine ⟨11354522402376551272704869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7569681601584367515136579 11354522402376551272704869)
                    ·
                      refine ⟨2128972950445603363632163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11354522402376551272704869 2128972950445603363632163)
                      ·
                        rfl

theorem cell23_4146160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_4146160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146160 prefixEnd_4146160 := by exact prefixLift 4146160
  have htrace : WordTrace (prefixWord ++ tailWord_4146160) baseStart_4146160 baseEnd_4146160 := by
    simpa [prefixWord, tailWord_4146160, baseEnd_4146160] using wordTrace_append hprefix tailTrace_4146160
  have hstable : (prefixWord ++ tailWord_4146160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146160).length < 2 ^ (prefixWord ++ tailWord_4146160).sum := by decide
  have hdescent : baseEnd_4146160 < baseStart_4146160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146177 : List Nat := [1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_4146177 : Nat := 118140960795 + 4146177 * 2 ^ 59
def prefixEnd_4146177 : Nat := 4983230072969 + 3 ^ 40 * 4146177 * 2
def baseEnd_4146177 : Nat := 2128981679616729797119585

theorem tailTrace_4146177 : CollatzResearch.WordTrace tailWord_4146177 prefixEnd_4146177 2128981679616729797119585 := by
  unfold tailWord_4146177
  simp only [CollatzResearch.WordTrace]
  refine ⟨151223498700116314501140785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100815665800077543000760523 151223498700116314501140785)
  ·
    refine ⟨113417624025087235875855589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151223498700116314501140785 113417624025087235875855589)
    ·
      refine ⟨21265804504703856726722923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113417624025087235875855589 21265804504703856726722923)
      ·
        refine ⟨31898706757055785090084385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21265804504703856726722923 31898706757055785090084385)
        ·
          refine ⟨23924030067791838817563289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31898706757055785090084385 23924030067791838817563289)
          ·
            refine ⟨17943022550843879113172467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23924030067791838817563289 17943022550843879113172467)
            ·
              refine ⟨26914533826265818669758701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17943022550843879113172467 26914533826265818669758701)
              ·
                refine ⟨10092950184849682001159513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26914533826265818669758701 10092950184849682001159513)
                ·
                  refine ⟨7569712638637261500869635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10092950184849682001159513 7569712638637261500869635)
                  ·
                    refine ⟨11354568957955892251304453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7569712638637261500869635 11354568957955892251304453)
                    ·
                      refine ⟨2128981679616729797119585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11354568957955892251304453 2128981679616729797119585)
                      ·
                        rfl

theorem cell23_4146177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_4146177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146177 prefixEnd_4146177 := by exact prefixLift 4146177
  have htrace : WordTrace (prefixWord ++ tailWord_4146177) baseStart_4146177 baseEnd_4146177 := by
    simpa [prefixWord, tailWord_4146177, baseEnd_4146177] using wordTrace_append hprefix tailTrace_4146177
  have hstable : (prefixWord ++ tailWord_4146177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146177).length < 2 ^ (prefixWord ++ tailWord_4146177).sum := by decide
  have hdescent : baseEnd_4146177 < baseStart_4146177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146238 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_4146238 : Nat := 118140960795 + 4146238 * 2 ^ 59
def prefixEnd_4146238 : Nat := 4983230072969 + 3 ^ 40 * 4146238 * 2
def baseEnd_4146238 : Nat := 709671000645551352818935

theorem tailTrace_4146238 : CollatzResearch.WordTrace tailWord_4146238 prefixEnd_4146238 709671000645551352818935 := by
  unfold tailWord_4146238
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903215444111915239888921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100817149035263547946074245 18903215444111915239888921)
  ·
    refine ⟨14177411583083936429916691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18903215444111915239888921 14177411583083936429916691)
    ·
      refine ⟨21266117374625904644875037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177411583083936429916691 21266117374625904644875037)
      ·
        refine ⟨7974794015484714241828139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21266117374625904644875037 7974794015484714241828139)
        ·
          refine ⟨11962191023227071362742209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974794015484714241828139 11962191023227071362742209)
          ·
            refine ⟨8971643267420303522056657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11962191023227071362742209 8971643267420303522056657)
            ·
              refine ⟨6728732450565227641542493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8971643267420303522056657 6728732450565227641542493)
              ·
                refine ⟨2523274668961960365578435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6728732450565227641542493 2523274668961960365578435)
                ·
                  refine ⟨3784912003442940548367653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523274668961960365578435 3784912003442940548367653)
                  ·
                    refine ⟨709671000645551352818935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3784912003442940548367653 709671000645551352818935)
                    ·
                      rfl

theorem cell23_4146238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_4146238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146238 prefixEnd_4146238 := by exact prefixLift 4146238
  have htrace : WordTrace (prefixWord ++ tailWord_4146238) baseStart_4146238 baseEnd_4146238 := by
    simpa [prefixWord, tailWord_4146238, baseEnd_4146238] using wordTrace_append hprefix tailTrace_4146238
  have hstable : (prefixWord ++ tailWord_4146238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146238).length < 2 ^ (prefixWord ++ tailWord_4146238).sum := by decide
  have hdescent : baseEnd_4146238 < baseStart_4146238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146254 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_4146254 : Nat := 118140960795 + 4146254 * 2 ^ 59
def prefixEnd_4146254 : Nat := 4983230072969 + 3 ^ 40 * 4146254 * 2
def baseEnd_4146254 : Nat := 2129021217627125995856731

theorem tailTrace_4146254 : CollatzResearch.WordTrace tailWord_4146254 prefixEnd_4146254 2129021217627125995856731 := by
  unfold tailWord_4146254
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903288390104669581461727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100817538080558237767795877 18903288390104669581461727)
  ·
    refine ⟨28354932585157004372192591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18903288390104669581461727 28354932585157004372192591)
    ·
      refine ⟨42532398877735506558288887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28354932585157004372192591 42532398877735506558288887)
      ·
        refine ⟨63798598316603259837433331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42532398877735506558288887 63798598316603259837433331)
        ·
          refine ⟨95697897474904889756149997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63798598316603259837433331 95697897474904889756149997)
          ·
            refine ⟨35886711553089333658556249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95697897474904889756149997 35886711553089333658556249)
            ·
              refine ⟨26915033664817000243917187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35886711553089333658556249 26915033664817000243917187)
              ·
                refine ⟨40372550497225500365875781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26915033664817000243917187 40372550497225500365875781)
                ·
                  refine ⟨7569853218229781318601709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40372550497225500365875781 7569853218229781318601709)
                  ·
                    refine ⟨2838694956836167994475641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7569853218229781318601709 2838694956836167994475641)
                    ·
                      refine ⟨2129021217627125995856731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838694956836167994475641 2129021217627125995856731)
                      ·
                        rfl

theorem cell23_4146254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_4146254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146254 prefixEnd_4146254 := by exact prefixLift 4146254
  have htrace : WordTrace (prefixWord ++ tailWord_4146254) baseStart_4146254 baseEnd_4146254 := by
    simpa [prefixWord, tailWord_4146254, baseEnd_4146254] using wordTrace_append hprefix tailTrace_4146254
  have hstable : (prefixWord ++ tailWord_4146254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146254).length < 2 ^ (prefixWord ++ tailWord_4146254).sum := by decide
  have hdescent : baseEnd_4146254 < baseStart_4146254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146261 : List Nat := [1, 3, 2, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_4146261 : Nat := 118140960795 + 4146261 * 2 ^ 59
def prefixEnd_4146261 : Nat := 4983230072969 + 3 ^ 40 * 4146261 * 2
def baseEnd_4146261 : Nat := 2129024811991707468469199

theorem tailTrace_4146261 : CollatzResearch.WordTrace tailWord_4146261 prefixEnd_4146261 2129024811991707468469199 := by
  unfold tailWord_4146261
  simp only [CollatzResearch.WordTrace]
  refine ⟨151226562431811996847198637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100817708287874664564799091 151226562431811996847198637)
  ·
    refine ⟨56709960911929498817699489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151226562431811996847198637 56709960911929498817699489)
    ·
      refine ⟨42532470683947124113274617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56709960911929498817699489 42532470683947124113274617)
      ·
        refine ⟨31899353012960343084955963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42532470683947124113274617 31899353012960343084955963)
        ·
          refine ⟨47849029519440514627433945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31899353012960343084955963 47849029519440514627433945)
          ·
            refine ⟨35886772139580385970575459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47849029519440514627433945 35886772139580385970575459)
            ·
              refine ⟨53830158209370578955863189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35886772139580385970575459 53830158209370578955863189)
              ·
                refine ⟨2523288666064245888556087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53830158209370578955863189 2523288666064245888556087)
                ·
                  refine ⟨3784932999096368832834131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523288666064245888556087 3784932999096368832834131)
                  ·
                    refine ⟨5677399498644553249251197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3784932999096368832834131 5677399498644553249251197)
                    ·
                      refine ⟨2129024811991707468469199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5677399498644553249251197 2129024811991707468469199)
                      ·
                        rfl

theorem cell23_4146261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_4146261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146261 prefixEnd_4146261 := by exact prefixLift 4146261
  have htrace : WordTrace (prefixWord ++ tailWord_4146261) baseStart_4146261 baseEnd_4146261 := by
    simpa [prefixWord, tailWord_4146261, baseEnd_4146261] using wordTrace_append hprefix tailTrace_4146261
  have hstable : (prefixWord ++ tailWord_4146261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146261).length < 2 ^ (prefixWord ++ tailWord_4146261).sum := by decide
  have hdescent : baseEnd_4146261 < baseStart_4146261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146284 : List Nat := [2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 4]
def baseStart_4146284 : Nat := 118140960795 + 4146284 * 2 ^ 59
def prefixEnd_4146284 : Nat := 4983230072969 + 3 ^ 40 * 4146284 * 2
def baseEnd_4146284 : Nat := 2129036622046760878481593

theorem tailTrace_4146284 : CollatzResearch.WordTrace tailWord_4146284 prefixEnd_4146284 2129036622046760878481593 := by
  unfold tailWord_4146284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75613700655364335887642953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100818267540485781183523937 75613700655364335887642953)
  ·
    refine ⟨56710275491523251915732215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75613700655364335887642953 56710275491523251915732215)
    ·
      refine ⟨85065413237284877873598323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56710275491523251915732215 85065413237284877873598323)
      ·
        refine ⟨127598119855927316810397485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85065413237284877873598323 127598119855927316810397485)
        ·
          refine ⟨47849294945972743803899057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127598119855927316810397485 47849294945972743803899057)
          ·
            refine ⟨35886971209479557852924293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47849294945972743803899057 35886971209479557852924293)
            ·
              refine ⟨6728807101777417097423305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35886971209479557852924293 6728807101777417097423305)
              ·
                refine ⟨5046605326333062823067479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728807101777417097423305 5046605326333062823067479)
                ·
                  refine ⟨7569907989499594234601219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046605326333062823067479 7569907989499594234601219)
                  ·
                    refine ⟨11354861984249391351901829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7569907989499594234601219 11354861984249391351901829)
                    ·
                      refine ⟨2129036622046760878481593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11354861984249391351901829 2129036622046760878481593)
                      ·
                        rfl

theorem cell23_4146284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 4].length) (baseStart_4146284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146284 prefixEnd_4146284 := by exact prefixLift 4146284
  have htrace : WordTrace (prefixWord ++ tailWord_4146284) baseStart_4146284 baseEnd_4146284 := by
    simpa [prefixWord, tailWord_4146284, baseEnd_4146284] using wordTrace_append hprefix tailTrace_4146284
  have hstable : (prefixWord ++ tailWord_4146284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146284).length < 2 ^ (prefixWord ++ tailWord_4146284).sum := by decide
  have hdescent : baseEnd_4146284 < baseStart_4146284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146294 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_4146294 : Nat := 118140960795 + 4146294 * 2 ^ 59
def prefixEnd_4146294 : Nat := 4983230072969 + 3 ^ 40 * 4146294 * 2
def baseEnd_4146294 : Nat := 709680585617768613118849

theorem tailTrace_4146294 : CollatzResearch.WordTrace tailWord_4146294 prefixEnd_4146294 709680585617768613118849 := by
  unfold tailWord_4146294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451735377543277717696871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100818510693794962322099957 9451735377543277717696871)
  ·
    refine ⟨14177603066314916576545307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9451735377543277717696871 14177603066314916576545307)
    ·
      refine ⟨21266404599472374864817961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177603066314916576545307 21266404599472374864817961)
      ·
        refine ⟨15949803449604281148613471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21266404599472374864817961 15949803449604281148613471)
        ·
          refine ⟨23924705174406421722920207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15949803449604281148613471 23924705174406421722920207)
          ·
            refine ⟨35887057761609632584380311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23924705174406421722920207 35887057761609632584380311)
            ·
              refine ⟨53830586642414448876570467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35887057761609632584380311 53830586642414448876570467)
              ·
                refine ⟨80745879963621673314855701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53830586642414448876570467 80745879963621673314855701)
                ·
                  refine ⟨3784963123294765936633861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80745879963621673314855701 3784963123294765936633861)
                  ·
                    refine ⟨709680585617768613118849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3784963123294765936633861 709680585617768613118849)
                    ·
                      rfl

theorem cell23_4146294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_4146294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146294 prefixEnd_4146294 := by exact prefixLift 4146294
  have htrace : WordTrace (prefixWord ++ tailWord_4146294) baseStart_4146294 baseEnd_4146294 := by
    simpa [prefixWord, tailWord_4146294, baseEnd_4146294] using wordTrace_append hprefix tailTrace_4146294
  have hstable : (prefixWord ++ tailWord_4146294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146294).length < 2 ^ (prefixWord ++ tailWord_4146294).sum := by decide
  have hdescent : baseEnd_4146294 < baseStart_4146294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146304 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3]
def baseStart_4146304 : Nat := 118140960795 + 4146304 * 2 ^ 59
def prefixEnd_4146304 : Nat := 4983230072969 + 3 ^ 40 * 4146304 * 2
def baseEnd_4146304 : Nat := 2129046891659850800231501

theorem tailTrace_4146304 : CollatzResearch.WordTrace tailWord_4146304 prefixEnd_4146304 2129046891659850800231501 := by
  unfold tailWord_4146304
  simp only [CollatzResearch.WordTrace]
  refine ⟨75614065385328107595506983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100818753847104143460675977 75614065385328107595506983)
  ·
    refine ⟨113421098077992161393260475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75614065385328107595506983 113421098077992161393260475)
    ·
      refine ⟨170131647116988242089890713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113421098077992161393260475 170131647116988242089890713)
      ·
        refine ⟨127598735337741181567418035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170131647116988242089890713 127598735337741181567418035)
        ·
          refine ⟨191398103006611772351127053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127598735337741181567418035 191398103006611772351127053)
          ·
            refine ⟨71774288627479414631672645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191398103006611772351127053 71774288627479414631672645)
            ·
              refine ⟨13457679117652390243438621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71774288627479414631672645 13457679117652390243438621)
              ·
                refine ⟨5046629669119646341289483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13457679117652390243438621 5046629669119646341289483)
                ·
                  refine ⟨7569944503679469511934225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046629669119646341289483 7569944503679469511934225)
                  ·
                    refine ⟨5677458377759602133950669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7569944503679469511934225 5677458377759602133950669)
                    ·
                      refine ⟨2129046891659850800231501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5677458377759602133950669 2129046891659850800231501)
                      ·
                        rfl

theorem cell23_4146304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_4146304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146304 prefixEnd_4146304 := by exact prefixLift 4146304
  have htrace : WordTrace (prefixWord ++ tailWord_4146304) baseStart_4146304 baseEnd_4146304 := by
    simpa [prefixWord, tailWord_4146304, baseEnd_4146304] using wordTrace_append hprefix tailTrace_4146304
  have hstable : (prefixWord ++ tailWord_4146304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146304).length < 2 ^ (prefixWord ++ tailWord_4146304).sum := by decide
  have hdescent : baseEnd_4146304 < baseStart_4146304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146318 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_4146318 : Nat := 118140960795 + 4146318 * 2 ^ 59
def prefixEnd_4146318 : Nat := 4983230072969 + 3 ^ 40 * 4146318 * 2
def baseEnd_4146318 : Nat := 2129054080389013745456437

theorem tailTrace_4146318 : CollatzResearch.WordTrace tailWord_4146318 prefixEnd_4146318 2129054080389013745456437 := by
  unfold tailWord_4146318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18903580174075686947752951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100819094261736997054682405 18903580174075686947752951)
  ·
    refine ⟨28355370261113530421629427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18903580174075686947752951 28355370261113530421629427)
    ·
      refine ⟨42533055391670295632444141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28355370261113530421629427 42533055391670295632444141)
      ·
        refine ⟨15949895771876360862166553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42533055391670295632444141 15949895771876360862166553)
        ·
          refine ⟨11962421828907270646624915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949895771876360862166553 11962421828907270646624915)
          ·
            refine ⟨17943632743360905969937373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962421828907270646624915 17943632743360905969937373)
            ·
              refine ⟨6728862278760339738726515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17943632743360905969937373 6728862278760339738726515)
              ·
                refine ⟨10093293418140509608089773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728862278760339738726515 10093293418140509608089773)
                ·
                  refine ⟨3784985031802691103033665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10093293418140509608089773 3784985031802691103033665)
                  ·
                    refine ⟨2838738773852018327275249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3784985031802691103033665 2838738773852018327275249)
                    ·
                      refine ⟨2129054080389013745456437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838738773852018327275249 2129054080389013745456437)
                      ·
                        rfl

theorem cell23_4146318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_4146318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146318 prefixEnd_4146318 := by exact prefixLift 4146318
  have htrace : WordTrace (prefixWord ++ tailWord_4146318) baseStart_4146318 baseEnd_4146318 := by
    simpa [prefixWord, tailWord_4146318, baseEnd_4146318] using wordTrace_append hprefix tailTrace_4146318
  have hstable : (prefixWord ++ tailWord_4146318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146318).length < 2 ^ (prefixWord ++ tailWord_4146318).sum := by decide
  have hdescent : baseEnd_4146318 < baseStart_4146318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146328 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 2, 4]
def baseStart_4146328 : Nat := 118140960795 + 4146328 * 2 ^ 59
def prefixEnd_4146328 : Nat := 4983230072969 + 3 ^ 40 * 4146328 * 2
def baseEnd_4146328 : Nat := 709686405065186235443797

theorem tailTrace_4146328 : CollatzResearch.WordTrace tailWord_4146328 prefixEnd_4146328 709686405065186235443797 := by
  unfold tailWord_4146328
  simp only [CollatzResearch.WordTrace]
  refine ⟨75614503061284633644943819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100819337415046178193258425 75614503061284633644943819)
  ·
    refine ⟨113421754591926950467415729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75614503061284633644943819 113421754591926950467415729)
    ·
      refine ⟨85066315943945212850561797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113421754591926950467415729 85066315943945212850561797)
      ·
        refine ⟨15949934239489727409480337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85066315943945212850561797 15949934239489727409480337)
        ·
          refine ⟨11962450679617295557110253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949934239489727409480337 11962450679617295557110253)
          ·
            refine ⟨4485919004856485833916345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11962450679617295557110253 4485919004856485833916345)
            ·
              refine ⟨3364439253642364375437259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4485919004856485833916345 3364439253642364375437259)
              ·
                refine ⟨5046658880463546563155889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364439253642364375437259 5046658880463546563155889)
                ·
                  refine ⟨3784994160347659922366917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5046658880463546563155889 3784994160347659922366917)
                  ·
                    refine ⟨709686405065186235443797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3784994160347659922366917 709686405065186235443797)
                    ·
                      rfl

theorem cell23_4146328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 4].length) (baseStart_4146328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146328 prefixEnd_4146328 := by exact prefixLift 4146328
  have htrace : WordTrace (prefixWord ++ tailWord_4146328) baseStart_4146328 baseEnd_4146328 := by
    simpa [prefixWord, tailWord_4146328, baseEnd_4146328] using wordTrace_append hprefix tailTrace_4146328
  have hstable : (prefixWord ++ tailWord_4146328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146328).length < 2 ^ (prefixWord ++ tailWord_4146328).sum := by decide
  have hdescent : baseEnd_4146328 < baseStart_4146328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146368 : List Nat := [2, 1, 1, 2, 6, 1, 2, 2, 2, 1, 3]
def baseStart_4146368 : Nat := 118140960795 + 4146368 * 2 ^ 59
def prefixEnd_4146368 : Nat := 4983230072969 + 3 ^ 40 * 4146368 * 2
def baseEnd_4146368 : Nat := 2129079754421738549831207

theorem tailTrace_4146368 : CollatzResearch.WordTrace tailWord_4146368 prefixEnd_4146368 2129079754421738549831207 := by
  unfold tailWord_4146368
  simp only [CollatzResearch.WordTrace]
  refine ⟨75615232521212177060671879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100820310028282902747562505 75615232521212177060671879)
  ·
    refine ⟨113422848781818265591007819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75615232521212177060671879 113422848781818265591007819)
    ·
      refine ⟨170134273172727398386511729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113422848781818265591007819 170134273172727398386511729)
      ·
        refine ⟨127600704879545548789883797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170134273172727398386511729 127600704879545548789883797)
        ·
          refine ⟨5981283041228697599525803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 127600704879545548789883797 5981283041228697599525803)
          ·
            refine ⟨8971924561843046399288705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981283041228697599525803 8971924561843046399288705)
            ·
              refine ⟨6728943421382284799466529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8971924561843046399288705 6728943421382284799466529)
              ·
                refine ⟨5046707566036713599599897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728943421382284799466529 5046707566036713599599897)
                ·
                  refine ⟨3785030674527535199699923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5046707566036713599599897 3785030674527535199699923)
                  ·
                    refine ⟨5677546011791302799549885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3785030674527535199699923 5677546011791302799549885)
                    ·
                      refine ⟨2129079754421738549831207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5677546011791302799549885 2129079754421738549831207)
                      ·
                        rfl

theorem cell23_4146368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_4146368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146368 prefixEnd_4146368 := by exact prefixLift 4146368
  have htrace : WordTrace (prefixWord ++ tailWord_4146368) baseStart_4146368 baseEnd_4146368 := by
    simpa [prefixWord, tailWord_4146368, baseEnd_4146368] using wordTrace_append hprefix tailTrace_4146368
  have hstable : (prefixWord ++ tailWord_4146368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146368).length < 2 ^ (prefixWord ++ tailWord_4146368).sum := by decide
  have hdescent : baseEnd_4146368 < baseStart_4146368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146369 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_4146369 : Nat := 118140960795 + 4146369 * 2 ^ 59
def prefixEnd_4146369 : Nat := 4983230072969 + 3 ^ 40 * 4146369 * 2
def baseEnd_4146369 : Nat := 2129080267902393045918703

theorem tailTrace_4146369 : CollatzResearch.WordTrace tailWord_4146369 prefixEnd_4146369 2129080267902393045918703 := by
  unfold tailWord_4146369
  simp only [CollatzResearch.WordTrace]
  refine ⟨151230501515420731292130161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100820334343613820861420107 151230501515420731292130161)
  ·
    refine ⟨113422876136565548469097621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151230501515420731292130161 113422876136565548469097621)
    ·
      refine ⟨5316697318901510084488951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113422876136565548469097621 5316697318901510084488951)
      ·
        refine ⟨7975045978352265126733427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316697318901510084488951 7975045978352265126733427)
        ·
          refine ⟨11962568967528397690100141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975045978352265126733427 11962568967528397690100141)
          ·
            refine ⟨4485963362823149133787553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11962568967528397690100141 4485963362823149133787553)
            ·
              refine ⟨3364472522117361850340665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4485963362823149133787553 3364472522117361850340665)
              ·
                refine ⟨2523354391588021387755499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3364472522117361850340665 2523354391588021387755499)
                ·
                  refine ⟨3785031587382032081633249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523354391588021387755499 3785031587382032081633249)
                  ·
                    refine ⟨2838773690536524061224937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3785031587382032081633249 2838773690536524061224937)
                    ·
                      refine ⟨2129080267902393045918703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838773690536524061224937 2129080267902393045918703)
                      ·
                        rfl

theorem cell23_4146369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_4146369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146369 prefixEnd_4146369 := by exact prefixLift 4146369
  have htrace : WordTrace (prefixWord ++ tailWord_4146369) baseStart_4146369 baseEnd_4146369 := by
    simpa [prefixWord, tailWord_4146369, baseEnd_4146369] using wordTrace_append hprefix tailTrace_4146369
  have hstable : (prefixWord ++ tailWord_4146369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146369).length < 2 ^ (prefixWord ++ tailWord_4146369).sum := by decide
  have hdescent : baseEnd_4146369 < baseStart_4146369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146387 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4]
def baseStart_4146387 : Nat := 118140960795 + 4146387 * 2 ^ 59
def prefixEnd_4146387 : Nat := 4983230072969 + 3 ^ 40 * 4146387 * 2
def baseEnd_4146387 : Nat := 2129089510554173975493619

theorem tailTrace_4146387 : CollatzResearch.WordTrace tailWord_4146387 prefixEnd_4146387 2129089510554173975493619 := by
  unfold tailWord_4146387
  simp only [CollatzResearch.WordTrace]
  refine ⟨151231158029355520366285415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100820772019570346910856943 151231158029355520366285415)
  ·
    refine ⟨226846737044033280549428123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151231158029355520366285415 226846737044033280549428123)
    ·
      refine ⟨340270105566049920824142185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226846737044033280549428123 340270105566049920824142185)
      ·
        refine ⟨255202579174537440618106639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340270105566049920824142185 255202579174537440618106639)
        ·
          refine ⟨382803868761806160927159959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255202579174537440618106639 382803868761806160927159959)
          ·
            refine ⟨574205803142709241390739939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382803868761806160927159959 574205803142709241390739939)
            ·
              refine ⟨861308704714063862086109909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574205803142709241390739939 861308704714063862086109909)
              ·
                refine ⟨20186922766735871767643201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 861308704714063862086109909 20186922766735871767643201)
                ·
                  refine ⟨15140192075051903825732401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20186922766735871767643201 15140192075051903825732401)
                  ·
                    refine ⟨11355144056288927869299301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15140192075051903825732401 11355144056288927869299301)
                    ·
                      refine ⟨2129089510554173975493619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11355144056288927869299301 2129089510554173975493619)
                      ·
                        rfl

theorem cell23_4146387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_4146387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146387 prefixEnd_4146387 := by exact prefixLift 4146387
  have htrace : WordTrace (prefixWord ++ tailWord_4146387) baseStart_4146387 baseEnd_4146387 := by
    simpa [prefixWord, tailWord_4146387, baseEnd_4146387] using wordTrace_append hprefix tailTrace_4146387
  have hstable : (prefixWord ++ tailWord_4146387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146387).length < 2 ^ (prefixWord ++ tailWord_4146387).sum := by decide
  have hdescent : baseEnd_4146387 < baseStart_4146387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146437 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 7]
def baseStart_4146437 : Nat := 118140960795 + 4146437 * 2 ^ 59
def prefixEnd_4146437 : Nat := 4983230072969 + 3 ^ 40 * 4146437 * 2
def baseEnd_4146437 : Nat := 2129115184586898779868389

theorem tailTrace_4146437 : CollatzResearch.WordTrace tailWord_4146437 prefixEnd_4146437 2129115184586898779868389 := by
  unfold tailWord_4146437
  simp only [CollatzResearch.WordTrace]
  refine ⟨151232981679174378905605565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100821987786116252603737043 151232981679174378905605565)
  ·
    refine ⟨56712368129690392089602087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151232981679174378905605565 56712368129690392089602087)
    ·
      refine ⟨85068552194535588134403131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56712368129690392089602087 85068552194535588134403131)
      ·
        refine ⟨127602828291803382201604697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85068552194535588134403131 127602828291803382201604697)
        ·
          refine ⟨95702121218852536651203523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127602828291803382201604697 95702121218852536651203523)
          ·
            refine ⟨143553181828278804976805285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95702121218852536651203523 143553181828278804976805285)
            ·
              refine ⟨26916221592802275933150991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143553181828278804976805285 26916221592802275933150991)
              ·
                refine ⟨40374332389203413899726487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26916221592802275933150991 40374332389203413899726487)
                ·
                  refine ⟨60561498583805120849589731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40374332389203413899726487 60561498583805120849589731)
                  ·
                    refine ⟨90842247875707681274384597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60561498583805120849589731 90842247875707681274384597)
                    ·
                      refine ⟨2129115184586898779868389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90842247875707681274384597 2129115184586898779868389)
                      ·
                        rfl

theorem cell23_4146437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_4146437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146437 prefixEnd_4146437 := by exact prefixLift 4146437
  have htrace : WordTrace (prefixWord ++ tailWord_4146437) baseStart_4146437 baseEnd_4146437 := by
    simpa [prefixWord, tailWord_4146437, baseEnd_4146437] using wordTrace_append hprefix tailTrace_4146437
  have hstable : (prefixWord ++ tailWord_4146437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146437).length < 2 ^ (prefixWord ++ tailWord_4146437).sum := by decide
  have hdescent : baseEnd_4146437 < baseStart_4146437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146481 : List Nat := [1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_4146481 : Nat := 118140960795 + 4146481 * 2 ^ 59
def prefixEnd_4146481 : Nat := 4983230072969 + 3 ^ 40 * 4146481 * 2
def baseEnd_4146481 : Nat := 2129137777735696607718187

theorem tailTrace_4146481 : CollatzResearch.WordTrace tailWord_4146481 prefixEnd_4146481 2129137777735696607718187 := by
  unfold tailWord_4146481
  simp only [CollatzResearch.WordTrace]
  refine ⟨151234586491014974420207297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100823057660676649613471531 151234586491014974420207297)
  ·
    refine ⟨113425939868261230815155473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151234586491014974420207297 113425939868261230815155473)
    ·
      refine ⟨85069454901195923111366605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113425939868261230815155473 85069454901195923111366605)
      ·
        refine ⟨31901045587948471166762477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85069454901195923111366605 31901045587948471166762477)
        ·
          refine ⟨11962892095480676687535929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31901045587948471166762477 11962892095480676687535929)
          ·
            refine ⟨8972169071610507515651947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11962892095480676687535929 8972169071610507515651947)
            ·
              refine ⟨13458253607415761273477921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972169071610507515651947 13458253607415761273477921)
              ·
                refine ⟨10093690205561820955108441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13458253607415761273477921 10093690205561820955108441)
                ·
                  refine ⟨7570267654171365716331331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10093690205561820955108441 7570267654171365716331331)
                  ·
                    refine ⟨11355401481257048574496997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7570267654171365716331331 11355401481257048574496997)
                    ·
                      refine ⟨2129137777735696607718187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11355401481257048574496997 2129137777735696607718187)
                      ·
                        rfl

theorem cell23_4146481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_4146481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146481 prefixEnd_4146481 := by exact prefixLift 4146481
  have htrace : WordTrace (prefixWord ++ tailWord_4146481) baseStart_4146481 baseEnd_4146481 := by
    simpa [prefixWord, tailWord_4146481, baseEnd_4146481] using wordTrace_append hprefix tailTrace_4146481
  have hstable : (prefixWord ++ tailWord_4146481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146481).length < 2 ^ (prefixWord ++ tailWord_4146481).sum := by decide
  have hdescent : baseEnd_4146481 < baseStart_4146481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146507 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8]
def baseStart_4146507 : Nat := 118140960795 + 4146507 * 2 ^ 59
def prefixEnd_4146507 : Nat := 4983230072969 + 3 ^ 40 * 4146507 * 2
def baseEnd_4146507 : Nat := 2129151128232713505993067

theorem tailTrace_4146507 : CollatzResearch.WordTrace tailWord_4146507 prefixEnd_4146507 2129151128232713505993067 := by
  unfold tailWord_4146507
  simp only [CollatzResearch.WordTrace]
  refine ⟨151235534788920780860653775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100823689859280520573769183 151235534788920780860653775)
  ·
    refine ⟨226853302183381171290980663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151235534788920780860653775 226853302183381171290980663)
    ·
      refine ⟨340279953275071756936470995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226853302183381171290980663 340279953275071756936470995)
      ·
        refine ⟨510419929912607635404706493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340279953275071756936470995 510419929912607635404706493)
        ·
          refine ⟨191407473717227863276764935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510419929912607635404706493 191407473717227863276764935)
          ·
            refine ⟨287111210575841794915147403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191407473717227863276764935 287111210575841794915147403)
            ·
              refine ⟨430666815863762692372721105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287111210575841794915147403 430666815863762692372721105)
              ·
                refine ⟨323000111897822019279540829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430666815863762692372721105 323000111897822019279540829)
                ·
                  refine ⟨121125041961683257229827811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323000111897822019279540829 121125041961683257229827811)
                  ·
                    refine ⟨181687562942524885844741717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121125041961683257229827811 181687562942524885844741717)
                    ·
                      refine ⟨2129151128232713505993067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 181687562942524885844741717 2129151128232713505993067)
                      ·
                        rfl

theorem cell23_4146507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 8].length) (baseStart_4146507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146507 prefixEnd_4146507 := by exact prefixLift 4146507
  have htrace : WordTrace (prefixWord ++ tailWord_4146507) baseStart_4146507 baseEnd_4146507 := by
    simpa [prefixWord, tailWord_4146507, baseEnd_4146507] using wordTrace_append hprefix tailTrace_4146507
  have hstable : (prefixWord ++ tailWord_4146507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146507).length < 2 ^ (prefixWord ++ tailWord_4146507).sum := by decide
  have hdescent : baseEnd_4146507 < baseStart_4146507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146538 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_4146538 : Nat := 118140960795 + 4146538 * 2 ^ 59
def prefixEnd_4146538 : Nat := 4983230072969 + 3 ^ 40 * 4146538 * 2
def baseEnd_4146538 : Nat := 236574116237000320522825

theorem tailTrace_4146538 : CollatzResearch.WordTrace tailWord_4146538 prefixEnd_4146538 236574116237000320522825 := by
  unfold tailWord_4146538
  simp only [CollatzResearch.WordTrace]
  refine ⟨37809166362952118288758067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100824443634538982103354845 37809166362952118288758067)
  ·
    refine ⟨56713749544428177433137101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37809166362952118288758067 56713749544428177433137101)
    ·
      refine ⟨21267656079160566537426413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56713749544428177433137101 21267656079160566537426413)
      ·
        refine ⟨7975371029685212451534905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21267656079160566537426413 7975371029685212451534905)
        ·
          refine ⟨5981528272263909338651179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7975371029685212451534905 5981528272263909338651179)
          ·
            refine ⟨8972292408395864007976769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981528272263909338651179 8972292408395864007976769)
            ·
              refine ⟨6729219306296898005982577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972292408395864007976769 6729219306296898005982577)
              ·
                refine ⟨5046914479722673504486933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6729219306296898005982577 5046914479722673504486933)
                ·
                  refine ⟨236574116237000320522825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5046914479722673504486933 236574116237000320522825)
                  ·
                    rfl

theorem cell23_4146538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_4146538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146538 prefixEnd_4146538 := by exact prefixLift 4146538
  have htrace : WordTrace (prefixWord ++ tailWord_4146538) baseStart_4146538 baseEnd_4146538 := by
    simpa [prefixWord, tailWord_4146538, baseEnd_4146538] using wordTrace_append hprefix tailTrace_4146538
  have hstable : (prefixWord ++ tailWord_4146538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146538).length < 2 ^ (prefixWord ++ tailWord_4146538).sum := by decide
  have hdescent : baseEnd_4146538 < baseStart_4146538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146542 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_4146542 : Nat := 118140960795 + 4146542 * 2 ^ 59
def prefixEnd_4146542 : Nat := 4983230072969 + 3 ^ 40 * 4146542 * 2
def baseEnd_4146542 : Nat := 709723033351873623018469

theorem tailTrace_4146542 : CollatzResearch.WordTrace tailWord_4146542 prefixEnd_4146542 709723033351873623018469 := by
  unfold tailWord_4146542
  simp only [CollatzResearch.WordTrace]
  refine ⟨18904601417974247729772235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100824540895862654558785253 18904601417974247729772235)
  ·
    refine ⟨28356902126961371594658353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18904601417974247729772235 28356902126961371594658353)
    ·
      refine ⟨21267676595221028695993765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28356902126961371594658353 21267676595221028695993765)
      ·
        refine ⟨3987689361603942880498831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21267676595221028695993765 3987689361603942880498831)
        ·
          refine ⟨5981534042405914320748247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987689361603942880498831 5981534042405914320748247)
          ·
            refine ⟨8972301063608871481122371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981534042405914320748247 8972301063608871481122371)
            ·
              refine ⟨13458451595413307221683557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972301063608871481122371 13458451595413307221683557)
              ·
                refine ⟨2523459674139995104065667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13458451595413307221683557 2523459674139995104065667)
                ·
                  refine ⟨3785189511209992656098501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523459674139995104065667 3785189511209992656098501)
                  ·
                    refine ⟨709723033351873623018469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785189511209992656098501 709723033351873623018469)
                    ·
                      rfl

theorem cell23_4146542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_4146542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146542 prefixEnd_4146542 := by exact prefixLift 4146542
  have htrace : WordTrace (prefixWord ++ tailWord_4146542) baseStart_4146542 baseEnd_4146542 := by
    simpa [prefixWord, tailWord_4146542, baseEnd_4146542] using wordTrace_append hprefix tailTrace_4146542
  have hstable : (prefixWord ++ tailWord_4146542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146542).length < 2 ^ (prefixWord ++ tailWord_4146542).sum := by decide
  have hdescent : baseEnd_4146542 < baseStart_4146542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146571 : List Nat := [1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 4]
def baseStart_4146571 : Nat := 118140960795 + 4146571 * 2 ^ 59
def prefixEnd_4146571 : Nat := 4983230072969 + 3 ^ 40 * 4146571 * 2
def baseEnd_4146571 : Nat := 2129183990994601255592773

theorem tailTrace_4146571 : CollatzResearch.WordTrace tailWord_4146571 prefixEnd_4146571 2129183990994601255592773 := by
  unfold tailWord_4146571
  simp only [CollatzResearch.WordTrace]
  refine ⟨151237869060688919790983567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100825246040459279860655711 151237869060688919790983567)
  ·
    refine ⟨226856803591033379686475351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151237869060688919790983567 226856803591033379686475351)
    ·
      refine ⟨340285205386550069529713027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226856803591033379686475351 340285205386550069529713027)
      ·
        refine ⟨510427808079825104294569541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340285205386550069529713027 510427808079825104294569541)
        ·
          refine ⟨95705214014967207055231789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510427808079825104294569541 95705214014967207055231789)
          ·
            refine ⟨35889455255612702645711921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95705214014967207055231789 35889455255612702645711921)
            ·
              refine ⟨26917091441709526984283941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35889455255612702645711921 26917091441709526984283941)
              ·
                refine ⟨5046954645320536309553239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26917091441709526984283941 5046954645320536309553239)
                ·
                  refine ⟨7570431967980804464329859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046954645320536309553239 7570431967980804464329859)
                  ·
                    refine ⟨11355647951971206696494789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7570431967980804464329859 11355647951971206696494789)
                    ·
                      refine ⟨2129183990994601255592773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11355647951971206696494789 2129183990994601255592773)
                      ·
                        rfl

theorem cell23_4146571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 1, 4].length) (baseStart_4146571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146571 prefixEnd_4146571 := by exact prefixLift 4146571
  have htrace : WordTrace (prefixWord ++ tailWord_4146571) baseStart_4146571 baseEnd_4146571 := by
    simpa [prefixWord, tailWord_4146571, baseEnd_4146571] using wordTrace_append hprefix tailTrace_4146571
  have hstable : (prefixWord ++ tailWord_4146571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146571).length < 2 ^ (prefixWord ++ tailWord_4146571).sum := by decide
  have hdescent : baseEnd_4146571 < baseStart_4146571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146624 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 2, 7]
def baseStart_4146624 : Nat := 118140960795 + 4146624 * 2 ^ 59
def prefixEnd_4146624 : Nat := 4983230072969 + 3 ^ 40 * 4146624 * 2
def baseEnd_4146624 : Nat := 709737068489763182743343

theorem tailTrace_4146624 : CollatzResearch.WordTrace tailWord_4146624 prefixEnd_4146624 709737068489763182743343 := by
  unfold tailWord_4146624
  simp only [CollatzResearch.WordTrace]
  refine ⟨75619901064748454921331463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100826534752997939895108617 75619901064748454921331463)
  ·
    refine ⟨113429851597122682381997195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75619901064748454921331463 113429851597122682381997195)
    ·
      refine ⟨170144777395684023572995793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113429851597122682381997195 170144777395684023572995793)
      ·
        refine ⟨127608583046763017679746845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170144777395684023572995793 127608583046763017679746845)
        ·
          refine ⟨47853218642536131629905067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127608583046763017679746845 47853218642536131629905067)
          ·
            refine ⟨71779827963804197444857601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47853218642536131629905067 71779827963804197444857601)
            ·
              refine ⟨53834870972853148083643201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71779827963804197444857601 53834870972853148083643201)
              ·
                refine ⟨40376153229639861062732401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53834870972853148083643201 40376153229639861062732401)
                ·
                  refine ⟨30282114922229895797049301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40376153229639861062732401 30282114922229895797049301)
                  ·
                    refine ⟨709737068489763182743343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30282114922229895797049301 709737068489763182743343)
                    ·
                      rfl

theorem cell23_4146624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 7].length) (baseStart_4146624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146624 prefixEnd_4146624 := by exact prefixLift 4146624
  have htrace : WordTrace (prefixWord ++ tailWord_4146624) baseStart_4146624 baseEnd_4146624 := by
    simpa [prefixWord, tailWord_4146624, baseEnd_4146624] using wordTrace_append hprefix tailTrace_4146624
  have hstable : (prefixWord ++ tailWord_4146624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146624).length < 2 ^ (prefixWord ++ tailWord_4146624).sum := by decide
  have hdescent : baseEnd_4146624 < baseStart_4146624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146628 : List Nat := [2, 3, 3, 2, 1, 1, 4, 7]
def baseStart_4146628 : Nat := 118140960795 + 4146628 * 2 ^ 59
def prefixEnd_4146628 : Nat := 4983230072969 + 3 ^ 40 * 4146628 * 2
def baseEnd_4146628 : Nat := 78859750347848427132593

theorem tailTrace_4146628 : CollatzResearch.WordTrace tailWord_4146628 prefixEnd_4146628 78859750347848427132593 := by
  unfold tailWord_4146628
  simp only [CollatzResearch.WordTrace]
  refine ⟨75619974010741209262904269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100826632014321612350539025 75619974010741209262904269)
  ·
    refine ⟨28357490254027953473589101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75619974010741209262904269 28357490254027953473589101)
    ·
      refine ⟨10634058845260482552595913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28357490254027953473589101 10634058845260482552595913)
      ·
        refine ⟨7975544133945361914446935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10634058845260482552595913 7975544133945361914446935)
        ·
          refine ⟨11963316200918042871670403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975544133945361914446935 11963316200918042871670403)
          ·
            refine ⟨17944974301377064307505605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963316200918042871670403 17944974301377064307505605)
            ·
              refine ⟨3364682681508199557657301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17944974301377064307505605 3364682681508199557657301)
              ·
                refine ⟨78859750347848427132593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3364682681508199557657301 78859750347848427132593)
                ·
                  rfl

theorem cell23_4146628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 7].length) (baseStart_4146628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146628 prefixEnd_4146628 := by exact prefixLift 4146628
  have htrace : WordTrace (prefixWord ++ tailWord_4146628) baseStart_4146628 baseEnd_4146628 := by
    simpa [prefixWord, tailWord_4146628, baseEnd_4146628] using wordTrace_append hprefix tailTrace_4146628
  have hstable : (prefixWord ++ tailWord_4146628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146628).length < 2 ^ (prefixWord ++ tailWord_4146628).sum := by decide
  have hdescent : baseEnd_4146628 < baseStart_4146628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146638 : List Nat := [4, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_4146638 : Nat := 118140960795 + 4146638 * 2 ^ 59
def prefixEnd_4146638 : Nat := 4983230072969 + 3 ^ 40 * 4146638 * 2
def baseEnd_4146638 : Nat := 2129218394198452493454965

theorem tailTrace_4146638 : CollatzResearch.WordTrace tailWord_4146638 prefixEnd_4146638 2129218394198452493454965 := by
  unfold tailWord_4146638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18905039093930773779209071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100826875167630793489115045 18905039093930773779209071)
  ·
    refine ⟨28357558640896160668813607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18905039093930773779209071 28357558640896160668813607)
    ·
      refine ⟨42536337961344241003220411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28357558640896160668813607 42536337961344241003220411)
      ·
        refine ⟨63804506942016361504830617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42536337961344241003220411 63804506942016361504830617)
        ·
          refine ⟨47853380206512271128622963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63804506942016361504830617 47853380206512271128622963)
          ·
            refine ⟨71780070309768406692934445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47853380206512271128622963 71780070309768406692934445)
            ·
              refine ⟨26917526366163152509850417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71780070309768406692934445 26917526366163152509850417)
              ·
                refine ⟨20188144774622364382387813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26917526366163152509850417 20188144774622364382387813)
                ·
                  refine ⟨3785277145241693321697715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20188144774622364382387813 3785277145241693321697715)
                  ·
                    refine ⟨5677915717862539982546573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3785277145241693321697715 5677915717862539982546573)
                    ·
                      refine ⟨2129218394198452493454965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5677915717862539982546573 2129218394198452493454965)
                      ·
                        rfl

theorem cell23_4146638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_4146638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146638 prefixEnd_4146638 := by exact prefixLift 4146638
  have htrace : WordTrace (prefixWord ++ tailWord_4146638) baseStart_4146638 baseEnd_4146638 := by
    simpa [prefixWord, tailWord_4146638, baseEnd_4146638] using wordTrace_append hprefix tailTrace_4146638
  have hstable : (prefixWord ++ tailWord_4146638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146638).length < 2 ^ (prefixWord ++ tailWord_4146638).sum := by decide
  have hdescent : baseEnd_4146638 < baseStart_4146638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146672 : List Nat := [2, 1, 1, 1, 3, 6, 2, 1, 2, 1, 3]
def baseStart_4146672 : Nat := 118140960795 + 4146672 * 2 ^ 59
def prefixEnd_4146672 : Nat := 4983230072969 + 3 ^ 40 * 4146672 * 2
def baseEnd_4146672 : Nat := 2129235852540705360429809

theorem tailTrace_4146672 : CollatzResearch.WordTrace tailWord_4146672 prefixEnd_4146672 2129235852540705360429809 := by
  unfold tailWord_4146672
  simp only [CollatzResearch.WordTrace]
  refine ⟨75620776416661507020205135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100827701888882009360273513 75620776416661507020205135)
  ·
    refine ⟨113431164624992260530307703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75620776416661507020205135 113431164624992260530307703)
    ·
      refine ⟨170146746937488390795461555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113431164624992260530307703 170146746937488390795461555)
      ·
        refine ⟨255220120406232586193192333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170146746937488390795461555 255220120406232586193192333)
        ·
          refine ⟨95707545152337219822447125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255220120406232586193192333 95707545152337219822447125)
          ·
            refine ⟨4486291179015807179177209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95707545152337219822447125 4486291179015807179177209)
            ·
              refine ⟨3364718384261855384382907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4486291179015807179177209 3364718384261855384382907)
              ·
                refine ⟨5047077576392783076574361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364718384261855384382907 5047077576392783076574361)
                ·
                  refine ⟨3785308182294587307430771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047077576392783076574361 3785308182294587307430771)
                  ·
                    refine ⟨5677962273441880961146157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3785308182294587307430771 5677962273441880961146157)
                    ·
                      refine ⟨2129235852540705360429809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5677962273441880961146157 2129235852540705360429809)
                      ·
                        rfl

theorem cell23_4146672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 2, 1, 3].length) (baseStart_4146672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146672 prefixEnd_4146672 := by exact prefixLift 4146672
  have htrace : WordTrace (prefixWord ++ tailWord_4146672) baseStart_4146672 baseEnd_4146672 := by
    simpa [prefixWord, tailWord_4146672, baseEnd_4146672] using wordTrace_append hprefix tailTrace_4146672
  have hstable : (prefixWord ++ tailWord_4146672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146672).length < 2 ^ (prefixWord ++ tailWord_4146672).sum := by decide
  have hdescent : baseEnd_4146672 < baseStart_4146672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146695 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_4146695 : Nat := 118140960795 + 4146695 * 2 ^ 59
def prefixEnd_4146695 : Nat := 4983230072969 + 3 ^ 40 * 4146695 * 2
def baseEnd_4146695 : Nat := 2129247662595758770442203

theorem tailTrace_4146695 : CollatzResearch.WordTrace tailWord_4146695 prefixEnd_4146695 2129247662595758770442203 := by
  unfold tailWord_4146695
  simp only [CollatzResearch.WordTrace]
  refine ⟨151242391712239688968497539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100828261141493125978998359 151242391712239688968497539)
  ·
    refine ⟨226863587568359533452746309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151242391712239688968497539 226863587568359533452746309)
    ·
      refine ⟨42536922669067412522389933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226863587568359533452746309 42536922669067412522389933)
      ·
        refine ⟨15951346000900279695896225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42536922669067412522389933 15951346000900279695896225)
        ·
          refine ⟨11963509500675209771922169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15951346000900279695896225 11963509500675209771922169)
          ·
            refine ⟨8972632125506407328941627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11963509500675209771922169 8972632125506407328941627)
            ·
              refine ⟨13458948188259610993412441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972632125506407328941627 13458948188259610993412441)
              ·
                refine ⟨10094211141194708245059331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13458948188259610993412441 10094211141194708245059331)
                ·
                  refine ⟨15141316711792062367588997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094211141194708245059331 15141316711792062367588997)
                  ·
                    refine ⟨2838996883461011693922937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15141316711792062367588997 2838996883461011693922937)
                    ·
                      refine ⟨2129247662595758770442203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2838996883461011693922937 2129247662595758770442203)
                      ·
                        rfl

theorem cell23_4146695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_4146695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146695 prefixEnd_4146695 := by exact prefixLift 4146695
  have htrace : WordTrace (prefixWord ++ tailWord_4146695) baseStart_4146695 baseEnd_4146695 := by
    simpa [prefixWord, tailWord_4146695, baseEnd_4146695] using wordTrace_append hprefix tailTrace_4146695
  have hstable : (prefixWord ++ tailWord_4146695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146695).length < 2 ^ (prefixWord ++ tailWord_4146695).sum := by decide
  have hdescent : baseEnd_4146695 < baseStart_4146695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146738 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_4146738 : Nat := 118140960795 + 4146738 * 2 ^ 59
def prefixEnd_4146738 : Nat := 4983230072969 + 3 ^ 40 * 4146738 * 2
def baseEnd_4146738 : Nat := 2129269742263902102204505

theorem tailTrace_4146738 : CollatzResearch.WordTrace tailWord_4146738 prefixEnd_4146738 2129269742263902102204505 := by
  unfold tailWord_4146738
  simp only [CollatzResearch.WordTrace]
  refine ⟨37810990012770976828078217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100829306700722604874875245 37810990012770976828078217)
  ·
    refine ⟨28358242509578232621058663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37810990012770976828078217 28358242509578232621058663)
    ·
      refine ⟨42537363764367348931587995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28358242509578232621058663 42537363764367348931587995)
      ·
        refine ⟨63806045646551023397381993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42537363764367348931587995 63806045646551023397381993)
        ·
          refine ⟨47854534234913267548036495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63806045646551023397381993 47854534234913267548036495)
          ·
            refine ⟨71781801352369901322054743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47854534234913267548036495 71781801352369901322054743)
            ·
              refine ⟨107672702028554851983082115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71781801352369901322054743 107672702028554851983082115)
              ·
                refine ⟨161509053042832277974623173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107672702028554851983082115 161509053042832277974623173)
                ·
                  refine ⟨30282947445531052120241845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161509053042832277974623173 30282947445531052120241845)
                  ·
                    refine ⟨2839026323018536136272673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30282947445531052120241845 2839026323018536136272673)
                    ·
                      refine ⟨2129269742263902102204505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839026323018536136272673 2129269742263902102204505)
                      ·
                        rfl

theorem cell23_4146738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_4146738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146738 prefixEnd_4146738 := by exact prefixLift 4146738
  have htrace : WordTrace (prefixWord ++ tailWord_4146738) baseStart_4146738 baseEnd_4146738 := by
    simpa [prefixWord, tailWord_4146738, baseEnd_4146738] using wordTrace_append hprefix tailTrace_4146738
  have hstable : (prefixWord ++ tailWord_4146738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146738).length < 2 ^ (prefixWord ++ tailWord_4146738).sum := by decide
  have hdescent : baseEnd_4146738 < baseStart_4146738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146748 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 1, 7]
def baseStart_4146748 : Nat := 118140960795 + 4146748 * 2 ^ 59
def prefixEnd_4146748 : Nat := 4983230072969 + 3 ^ 40 * 4146748 * 2
def baseEnd_4146748 : Nat := 709758292356815687693153

theorem tailTrace_4146748 : CollatzResearch.WordTrace tailWord_4146748 prefixEnd_4146748 709758292356815687693153 := by
  unfold tailWord_4146748
  simp only [CollatzResearch.WordTrace]
  refine ⟨75622162390523839510088449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100829549854031786013451265 75622162390523839510088449)
  ·
    refine ⟨56716621792892879632566337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75622162390523839510088449 56716621792892879632566337)
    ·
      refine ⟨42537466344669659724424753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56716621792892879632566337 42537466344669659724424753)
      ·
        refine ⟨31903099758502244793318565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42537466344669659724424753 31903099758502244793318565)
        ·
          refine ⟨5981831204719170898747231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31903099758502244793318565 5981831204719170898747231)
          ·
            refine ⟨8972746807078756348120847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981831204719170898747231 8972746807078756348120847)
            ·
              refine ⟨13459120210618134522181271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972746807078756348120847 13459120210618134522181271)
              ·
                refine ⟨20188680315927201783271907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13459120210618134522181271 20188680315927201783271907)
                ·
                  refine ⟨30283020473890802674907861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20188680315927201783271907 30283020473890802674907861)
                  ·
                    refine ⟨709758292356815687693153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30283020473890802674907861 709758292356815687693153)
                    ·
                      rfl

theorem cell23_4146748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_4146748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146748 prefixEnd_4146748 := by exact prefixLift 4146748
  have htrace : WordTrace (prefixWord ++ tailWord_4146748) baseStart_4146748 baseEnd_4146748 := by
    simpa [prefixWord, tailWord_4146748, baseEnd_4146748] using wordTrace_append hprefix tailTrace_4146748
  have hstable : (prefixWord ++ tailWord_4146748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146748).length < 2 ^ (prefixWord ++ tailWord_4146748).sum := by decide
  have hdescent : baseEnd_4146748 < baseStart_4146748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146768 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 4, 4, 2]
def baseStart_4146768 : Nat := 118140960795 + 4146768 * 2 ^ 59
def prefixEnd_4146768 : Nat := 4983230072969 + 3 ^ 40 * 4146768 * 2
def baseEnd_4146768 : Nat := 2129285146683536984829367

theorem tailTrace_4146768 : CollatzResearch.WordTrace tailWord_4146768 prefixEnd_4146768 2129285146683536984829367 := by
  unfold tailWord_4146768
  simp only [CollatzResearch.WordTrace]
  refine ⟨75622527120487611217952479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100830036160650148290603305 75622527120487611217952479)
  ·
    refine ⟨113433790680731416826928719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75622527120487611217952479 113433790680731416826928719)
    ·
      refine ⟨170150686021097125240393079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113433790680731416826928719 170150686021097125240393079)
      ·
        refine ⟨255226029031645687860589619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170150686021097125240393079 255226029031645687860589619)
        ·
          refine ⟨382839043547468531790884429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255226029031645687860589619 382839043547468531790884429)
          ·
            refine ⟨143564641330300699421581661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382839043547468531790884429 143564641330300699421581661)
            ·
              refine ⟨53836740498862762283093123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143564641330300699421581661 53836740498862762283093123)
              ·
                refine ⟨80755110748294143424639685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53836740498862762283093123 80755110748294143424639685)
                ·
                  refine ⟨15141583265305151892119941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80755110748294143424639685 15141583265305151892119941)
                  ·
                    refine ⟨2839046862244715979772489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15141583265305151892119941 2839046862244715979772489)
                    ·
                      refine ⟨2129285146683536984829367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839046862244715979772489 2129285146683536984829367)
                      ·
                        rfl

theorem cell23_4146768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 4, 4, 2].length) (baseStart_4146768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146768 prefixEnd_4146768 := by exact prefixLift 4146768
  have htrace : WordTrace (prefixWord ++ tailWord_4146768) baseStart_4146768 baseEnd_4146768 := by
    simpa [prefixWord, tailWord_4146768, baseEnd_4146768] using wordTrace_append hprefix tailTrace_4146768
  have hstable : (prefixWord ++ tailWord_4146768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146768).length < 2 ^ (prefixWord ++ tailWord_4146768).sum := by decide
  have hdescent : baseEnd_4146768 < baseStart_4146768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146771 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 3]
def baseStart_4146771 : Nat := 118140960795 + 4146771 * 2 ^ 59
def prefixEnd_4146771 : Nat := 4983230072969 + 3 ^ 40 * 4146771 * 2
def baseEnd_4146771 : Nat := 2129286687125500473091853

theorem tailTrace_4146771 : CollatzResearch.WordTrace tailWord_4146771 prefixEnd_4146771 2129286687125500473091853 := by
  unfold tailWord_4146771
  simp only [CollatzResearch.WordTrace]
  refine ⟨151245163659964353948264167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100830109106642902632176111 151245163659964353948264167)
  ·
    refine ⟨226867745489946530922396251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151245163659964353948264167 226867745489946530922396251)
    ·
      refine ⟨340301618234919796383594377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226867745489946530922396251 340301618234919796383594377)
      ·
        refine ⟨255226213676189847287695783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340301618234919796383594377 255226213676189847287695783)
        ·
          refine ⟨382839320514284770931543675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255226213676189847287695783 382839320514284770931543675)
          ·
            refine ⟨574258980771427156397315513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382839320514284770931543675 574258980771427156397315513)
            ·
              refine ⟨430694235578570367297986635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574258980771427156397315513 430694235578570367297986635)
              ·
                refine ⟨646041353367855550946979953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430694235578570367297986635 646041353367855550946979953)
                ·
                  refine ⟨484531015025891663210234965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 646041353367855550946979953 484531015025891663210234965)
                  ·
                    refine ⟨5678097832334667928244941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 484531015025891663210234965 5678097832334667928244941)
                    ·
                      refine ⟨2129286687125500473091853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678097832334667928244941 2129286687125500473091853)
                      ·
                        rfl

theorem cell23_4146771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_4146771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146771 prefixEnd_4146771 := by exact prefixLift 4146771
  have htrace : WordTrace (prefixWord ++ tailWord_4146771) baseStart_4146771 baseEnd_4146771 := by
    simpa [prefixWord, tailWord_4146771, baseEnd_4146771] using wordTrace_append hprefix tailTrace_4146771
  have hstable : (prefixWord ++ tailWord_4146771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146771).length < 2 ^ (prefixWord ++ tailWord_4146771).sum := by decide
  have hdescent : baseEnd_4146771 < baseStart_4146771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146788 : List Nat := [2, 3, 1, 1, 2, 3, 1, 2, 1, 4, 3]
def baseStart_4146788 : Nat := 118140960795 + 4146788 * 2 ^ 59
def prefixEnd_4146788 : Nat := 4983230072969 + 3 ^ 40 * 4146788 * 2
def baseEnd_4146788 : Nat := 2129295416296626906579275

theorem tailTrace_4146788 : CollatzResearch.WordTrace tailWord_4146788 prefixEnd_4146788 2129295416296626906579275 := by
  unfold tailWord_4146788
  simp only [CollatzResearch.WordTrace]
  refine ⟨75622891850451382925816509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100830522467268510567755345 75622891850451382925816509)
  ·
    refine ⟨28358584443919268597181191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75622891850451382925816509 28358584443919268597181191)
    ·
      refine ⟨42537876665878902895771787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28358584443919268597181191 42537876665878902895771787)
      ·
        refine ⟨63806814998818354343657681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42537876665878902895771787 63806814998818354343657681)
        ·
          refine ⟨47855111249113765757743261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63806814998818354343657681 47855111249113765757743261)
          ·
            refine ⟨17945666718417662159153723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47855111249113765757743261 17945666718417662159153723)
            ·
              refine ⟨26918500077626493238730585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17945666718417662159153723 26918500077626493238730585)
              ·
                refine ⟨20188875058219869929047939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26918500077626493238730585 20188875058219869929047939)
                ·
                  refine ⟨30283312587329804893571909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20188875058219869929047939 30283312587329804893571909)
                  ·
                    refine ⟨5678121110124338417544733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30283312587329804893571909 5678121110124338417544733)
                    ·
                      refine ⟨2129295416296626906579275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678121110124338417544733 2129295416296626906579275)
                      ·
                        rfl

theorem cell23_4146788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_4146788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146788 prefixEnd_4146788 := by exact prefixLift 4146788
  have htrace : WordTrace (prefixWord ++ tailWord_4146788) baseStart_4146788 baseEnd_4146788 := by
    simpa [prefixWord, tailWord_4146788, baseEnd_4146788] using wordTrace_append hprefix tailTrace_4146788
  have hstable : (prefixWord ++ tailWord_4146788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146788).length < 2 ^ (prefixWord ++ tailWord_4146788).sum := by decide
  have hdescent : baseEnd_4146788 < baseStart_4146788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146805 : List Nat := [1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_4146805 : Nat := 118140960795 + 4146805 * 2 ^ 59
def prefixEnd_4146805 : Nat := 4983230072969 + 3 ^ 40 * 4146805 * 2
def baseEnd_4146805 : Nat := 2129304145467753340066697

theorem tailTrace_4146805 : CollatzResearch.WordTrace tailWord_4146805 prefixEnd_4146805 2129304145467753340066697 := by
  unfold tailWord_4146805
  simp only [CollatzResearch.WordTrace]
  refine ⟨151246403741841177755001869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100830935827894118503334579 151246403741841177755001869)
  ·
    refine ⟨56717401403190441658125701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151246403741841177755001869 56717401403190441658125701)
    ·
      refine ⟨10634512763098207810898569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56717401403190441658125701 10634512763098207810898569)
      ·
        refine ⟨7975884572323655858173927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10634512763098207810898569 7975884572323655858173927)
        ·
          refine ⟨11963826858485483787260891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975884572323655858173927 11963826858485483787260891)
          ·
            refine ⟨17945740287728225680891337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963826858485483787260891 17945740287728225680891337)
            ·
              refine ⟨13459305215796169260668503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17945740287728225680891337 13459305215796169260668503)
              ·
                refine ⟨20188957823694253891002755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13459305215796169260668503 20188957823694253891002755)
                ·
                  refine ⟨30283436735541380836504133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20188957823694253891002755 30283436735541380836504133)
                  ·
                    refine ⟨5678144387914008906844525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30283436735541380836504133 5678144387914008906844525)
                    ·
                      refine ⟨2129304145467753340066697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678144387914008906844525 2129304145467753340066697)
                      ·
                        rfl

theorem cell23_4146805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_4146805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146805 prefixEnd_4146805 := by exact prefixLift 4146805
  have htrace : WordTrace (prefixWord ++ tailWord_4146805) baseStart_4146805 baseEnd_4146805 := by
    simpa [prefixWord, tailWord_4146805, baseEnd_4146805] using wordTrace_append hprefix tailTrace_4146805
  have hstable : (prefixWord ++ tailWord_4146805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146805).length < 2 ^ (prefixWord ++ tailWord_4146805).sum := by decide
  have hdescent : baseEnd_4146805 < baseStart_4146805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146845 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_4146845 : Nat := 118140960795 + 4146845 * 2 ^ 59
def prefixEnd_4146845 : Nat := 4983230072969 + 3 ^ 40 * 4146845 * 2
def baseEnd_4146845 : Nat := 2129324684693933183566513

theorem tailTrace_4146845 : CollatzResearch.WordTrace tailWord_4146845 prefixEnd_4146845 2129324684693933183566513 := by
  unfold tailWord_4146845
  simp only [CollatzResearch.WordTrace]
  refine ⟨151247862661696264586457989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100831908441130843057638659 151247862661696264586457989)
  ·
    refine ⟨28358974249068049609960873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151247862661696264586457989 28358974249068049609960873)
    ·
      refine ⟨21269230686801037207470655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28358974249068049609960873 21269230686801037207470655)
      ·
        refine ⟨31903846030201555811205983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21269230686801037207470655 31903846030201555811205983)
        ·
          refine ⟨47855769045302333716808975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31903846030201555811205983 47855769045302333716808975)
          ·
            refine ⟨71783653567953500575213463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47855769045302333716808975 71783653567953500575213463)
            ·
              refine ⟨107675480351930250862820195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71783653567953500575213463 107675480351930250862820195)
              ·
                refine ⟨161513220527895376294230293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107675480351930250862820195 161513220527895376294230293)
                ·
                  refine ⟨7570932212245095763792045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 161513220527895376294230293 7570932212245095763792045)
                  ·
                    refine ⟨2839099579591910911422017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7570932212245095763792045 2839099579591910911422017)
                    ·
                      refine ⟨2129324684693933183566513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839099579591910911422017 2129324684693933183566513)
                      ·
                        rfl

theorem cell23_4146845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_4146845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146845 prefixEnd_4146845 := by exact prefixLift 4146845
  have htrace : WordTrace (prefixWord ++ tailWord_4146845) baseStart_4146845 baseEnd_4146845 := by
    simpa [prefixWord, tailWord_4146845, baseEnd_4146845] using wordTrace_append hprefix tailTrace_4146845
  have hstable : (prefixWord ++ tailWord_4146845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146845).length < 2 ^ (prefixWord ++ tailWord_4146845).sum := by decide
  have hdescent : baseEnd_4146845 < baseStart_4146845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146856 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4146856 : Nat := 118140960795 + 4146856 * 2 ^ 59
def prefixEnd_4146856 : Nat := 4983230072969 + 3 ^ 40 * 4146856 * 2
def baseEnd_4146856 : Nat := 2129330332981132640528963

theorem tailTrace_4146856 : CollatzResearch.WordTrace tailWord_4146856 prefixEnd_4146856 2129330332981132640528963 := by
  unfold tailWord_4146856
  simp only [CollatzResearch.WordTrace]
  refine ⟨75624131932328206732554211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100832175909770942310072281 75624131932328206732554211)
  ·
    refine ⟨113436197898492310098831317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75624131932328206732554211 113436197898492310098831317)
    ·
      refine ⟨2658660888245913517941359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 113436197898492310098831317 2658660888245913517941359)
      ·
        refine ⟨3987991332368870276912039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2658660888245913517941359 3987991332368870276912039)
        ·
          refine ⟨5981986998553305415368059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3987991332368870276912039 5981986998553305415368059)
          ·
            refine ⟨8972980497829958123052089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981986998553305415368059 8972980497829958123052089)
            ·
              refine ⟨6729735373372468592289067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972980497829958123052089 6729735373372468592289067)
              ·
                refine ⟨10094603060058702888433601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729735373372468592289067 10094603060058702888433601)
                ·
                  refine ⟨7570952295044027166325201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10094603060058702888433601 7570952295044027166325201)
                  ·
                    refine ⟨5678214221283020374743901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7570952295044027166325201 5678214221283020374743901)
                    ·
                      refine ⟨2129330332981132640528963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678214221283020374743901 2129330332981132640528963)
                      ·
                        rfl

theorem cell23_4146856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4146856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146856 prefixEnd_4146856 := by exact prefixLift 4146856
  have htrace : WordTrace (prefixWord ++ tailWord_4146856) baseStart_4146856 baseEnd_4146856 := by
    simpa [prefixWord, tailWord_4146856, baseEnd_4146856] using wordTrace_append hprefix tailTrace_4146856
  have hstable : (prefixWord ++ tailWord_4146856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146856).length < 2 ^ (prefixWord ++ tailWord_4146856).sum := by decide
  have hdescent : baseEnd_4146856 < baseStart_4146856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146888 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 3, 2, 4]
def baseStart_4146888 : Nat := 118140960795 + 4146888 * 2 ^ 59
def prefixEnd_4146888 : Nat := 4983230072969 + 3 ^ 40 * 4146888 * 2
def baseEnd_4146888 : Nat := 2129346764362076515328815

theorem tailTrace_4146888 : CollatzResearch.WordTrace tailWord_4146888 prefixEnd_4146888 2129346764362076515328815 := by
  unfold tailWord_4146888
  simp only [CollatzResearch.WordTrace]
  refine ⟨75624715500270241465136659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100832954000360321953515545 75624715500270241465136659)
  ·
    refine ⟨113437073250405362197704989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75624715500270241465136659 113437073250405362197704989)
    ·
      refine ⟨42538902468902010824139371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113437073250405362197704989 42538902468902010824139371)
      ·
        refine ⟨63808353703353016236209057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42538902468902010824139371 63808353703353016236209057)
        ·
          refine ⟨47856265277514762177156793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63808353703353016236209057 47856265277514762177156793)
          ·
            refine ⟨35892198958136071632867595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47856265277514762177156793 35892198958136071632867595)
            ·
              refine ⟨53838298437204107449301393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35892198958136071632867595 53838298437204107449301393)
              ·
                refine ⟨40378723827903080586976045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53838298437204107449301393 40378723827903080586976045)
                ·
                  refine ⟨15142021435463655220116017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40378723827903080586976045 15142021435463655220116017)
                  ·
                    refine ⟨11356516076597741415087013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15142021435463655220116017 11356516076597741415087013)
                    ·
                      refine ⟨2129346764362076515328815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11356516076597741415087013 2129346764362076515328815)
                      ·
                        rfl

theorem cell23_4146888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_4146888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146888 prefixEnd_4146888 := by exact prefixLift 4146888
  have htrace : WordTrace (prefixWord ++ tailWord_4146888) baseStart_4146888 baseEnd_4146888 := by
    simpa [prefixWord, tailWord_4146888, baseEnd_4146888] using wordTrace_append hprefix tailTrace_4146888
  have hstable : (prefixWord ++ tailWord_4146888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146888).length < 2 ^ (prefixWord ++ tailWord_4146888).sum := by decide
  have hdescent : baseEnd_4146888 < baseStart_4146888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146905 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_4146905 : Nat := 118140960795 + 4146905 * 2 ^ 59
def prefixEnd_4146905 : Nat := 4983230072969 + 3 ^ 40 * 4146905 * 2
def baseEnd_4146905 : Nat := 2129355493533202948816237

theorem tailTrace_4146905 : CollatzResearch.WordTrace tailWord_4146905 prefixEnd_4146905 2129355493533202948816237 := by
  unfold tailWord_4146905
  simp only [CollatzResearch.WordTrace]
  refine ⟨151250051041478894833642169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100833367360985929889094779 151250051041478894833642169)
  ·
    refine ⟨113437538281109171125231627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151250051041478894833642169 113437538281109171125231627)
    ·
      refine ⟨170156307421663756687847441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113437538281109171125231627 170156307421663756687847441)
      ·
        refine ⟨127617230566247817515885581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170156307421663756687847441 127617230566247817515885581)
        ·
          refine ⟨47856461462342931568457093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127617230566247817515885581 47856461462342931568457093)
          ·
            refine ⟨8973086524189299669085705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47856461462342931568457093 8973086524189299669085705)
            ·
              refine ⟨6729814893141974751814279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973086524189299669085705 6729814893141974751814279)
              ·
                refine ⟨10094722339712962127721419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729814893141974751814279 10094722339712962127721419)
                ·
                  refine ⟨15142083509569443191582129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10094722339712962127721419 15142083509569443191582129)
                  ·
                    refine ⟨11356562632177082393686597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15142083509569443191582129 11356562632177082393686597)
                    ·
                      refine ⟨2129355493533202948816237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11356562632177082393686597 2129355493533202948816237)
                      ·
                        rfl

theorem cell23_4146905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_4146905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146905 prefixEnd_4146905 := by exact prefixLift 4146905
  have htrace : WordTrace (prefixWord ++ tailWord_4146905) baseStart_4146905 baseEnd_4146905 := by
    simpa [prefixWord, tailWord_4146905, baseEnd_4146905] using wordTrace_append hprefix tailTrace_4146905
  have hstable : (prefixWord ++ tailWord_4146905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146905).length < 2 ^ (prefixWord ++ tailWord_4146905).sum := by decide
  have hdescent : baseEnd_4146905 < baseStart_4146905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146926 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_4146926 : Nat := 118140960795 + 4146926 * 2 ^ 59
def prefixEnd_4146926 : Nat := 4983230072969 + 3 ^ 40 * 4146926 * 2
def baseEnd_4146926 : Nat := 2129366276626947366653641

theorem tailTrace_4146926 : CollatzResearch.WordTrace tailWord_4146926 prefixEnd_4146926 2129366276626947366653641 := by
  unfold tailWord_4146926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18906352121800351927519579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100833877982935210280104421 18906352121800351927519579)
  ·
    refine ⟨28359528182700527891279369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18906352121800351927519579 28359528182700527891279369)
    ·
      refine ⟨21269646137025395918459527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28359528182700527891279369 21269646137025395918459527)
      ·
        refine ⟨31904469205538093877689291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21269646137025395918459527 31904469205538093877689291)
        ·
          refine ⟨47856703808307140816533937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31904469205538093877689291 47856703808307140816533937)
          ·
            refine ⟨35892527856230355612400453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47856703808307140816533937 35892527856230355612400453)
            ·
              refine ⟨6729848973043191677325085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35892527856230355612400453 6729848973043191677325085)
              ·
                refine ⟨2523693364891196878996907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6729848973043191677325085 2523693364891196878996907)
                ·
                  refine ⟨3785540047336795318495361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2523693364891196878996907 3785540047336795318495361)
                  ·
                    refine ⟨2839155035502596488871521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3785540047336795318495361 2839155035502596488871521)
                    ·
                      refine ⟨2129366276626947366653641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839155035502596488871521 2129366276626947366653641)
                      ·
                        rfl

theorem cell23_4146926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_4146926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146926 prefixEnd_4146926 := by exact prefixLift 4146926
  have htrace : WordTrace (prefixWord ++ tailWord_4146926) baseStart_4146926 baseEnd_4146926 := by
    simpa [prefixWord, tailWord_4146926, baseEnd_4146926] using wordTrace_append hprefix tailTrace_4146926
  have hstable : (prefixWord ++ tailWord_4146926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146926).length < 2 ^ (prefixWord ++ tailWord_4146926).sum := by decide
  have hdescent : baseEnd_4146926 < baseStart_4146926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146929 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 1, 2, 3]
def baseStart_4146929 : Nat := 118140960795 + 4146929 * 2 ^ 59
def prefixEnd_4146929 : Nat := 4983230072969 + 3 ^ 40 * 4146929 * 2
def baseEnd_4146929 : Nat := 2129367817068910854916127

theorem tailTrace_4146929 : CollatzResearch.WordTrace tailWord_4146929 prefixEnd_4146929 2129367817068910854916127 := by
  unfold tailWord_4146929
  simp only [CollatzResearch.WordTrace]
  refine ⟨151250926393391946932515841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100833950928927964621677227 151250926393391946932515841)
  ·
    refine ⟨113438194795043960199386881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151250926393391946932515841 113438194795043960199386881)
    ·
      refine ⟨85078646096282970149540161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113438194795043960199386881 85078646096282970149540161)
      ·
        refine ⟨63808984572212227612155121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85078646096282970149540161 63808984572212227612155121)
        ·
          refine ⟨47856738429159170709116341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63808984572212227612155121 47856738429159170709116341)
          ·
            refine ⟨4486569227733672253979657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47856738429159170709116341 4486569227733672253979657)
            ·
              refine ⟨3364926920800254190484743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4486569227733672253979657 3364926920800254190484743)
              ·
                refine ⟨5047390381200381285727115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364926920800254190484743 5047390381200381285727115)
                ·
                  refine ⟨7571085571800571928590673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5047390381200381285727115 7571085571800571928590673)
                  ·
                    refine ⟨5678314178850428946443005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7571085571800571928590673 5678314178850428946443005)
                    ·
                      refine ⟨2129367817068910854916127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678314178850428946443005 2129367817068910854916127)
                      ·
                        rfl

theorem cell23_4146929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_4146929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146929 prefixEnd_4146929 := by exact prefixLift 4146929
  have htrace : WordTrace (prefixWord ++ tailWord_4146929) baseStart_4146929 baseEnd_4146929 := by
    simpa [prefixWord, tailWord_4146929, baseEnd_4146929] using wordTrace_append hprefix tailTrace_4146929
  have hstable : (prefixWord ++ tailWord_4146929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146929).length < 2 ^ (prefixWord ++ tailWord_4146929).sum := by decide
  have hdescent : baseEnd_4146929 < baseStart_4146929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4146932 : List Nat := [2, 6, 1, 1, 1, 2, 10]
def baseStart_4146932 : Nat := 118140960795 + 4146932 * 2 ^ 59
def prefixEnd_4146932 : Nat := 4983230072969 + 3 ^ 40 * 4146932 * 2
def baseEnd_4146932 : Nat := 26288510586554004236773

theorem tailTrace_4146932 : CollatzResearch.WordTrace tailWord_4146932 prefixEnd_4146932 26288510586554004236773 := by
  unfold tailWord_4146932
  simp only [CollatzResearch.WordTrace]
  refine ⟨75625517906190539222437525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100834023874920718963250033 75625517906190539222437525)
  ·
    refine ⟨3544946151852681526051759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75625517906190539222437525 3544946151852681526051759)
    ·
      refine ⟨5317419227779022289077639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3544946151852681526051759 5317419227779022289077639)
      ·
        refine ⟨7976128841668533433616459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5317419227779022289077639 7976128841668533433616459)
        ·
          refine ⟨11964193262502800150424689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7976128841668533433616459 11964193262502800150424689)
          ·
            refine ⟨8973144946877100112818517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11964193262502800150424689 8973144946877100112818517)
            ·
              refine ⟨26288510586554004236773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8973144946877100112818517 26288510586554004236773)
              ·
                rfl

theorem cell23_4146932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 10].length) (baseStart_4146932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4146932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4146932 prefixEnd_4146932 := by exact prefixLift 4146932
  have htrace : WordTrace (prefixWord ++ tailWord_4146932) baseStart_4146932 baseEnd_4146932 := by
    simpa [prefixWord, tailWord_4146932, baseEnd_4146932] using wordTrace_append hprefix tailTrace_4146932
  have hstable : (prefixWord ++ tailWord_4146932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4146932).length < 2 ^ (prefixWord ++ tailWord_4146932).sum := by decide
  have hdescent : baseEnd_4146932 < baseStart_4146932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4146932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147015 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_4147015 : Nat := 118140960795 + 4147015 * 2 ^ 59
def prefixEnd_4147015 : Nat := 4983230072969 + 3 ^ 40 * 4147015 * 2
def baseEnd_4147015 : Nat := 2129411976405197518440731

theorem tailTrace_4147015 : CollatzResearch.WordTrace tailWord_4147015 prefixEnd_4147015 2129411976405197518440731 := by
  unfold tailWord_4147015
  simp only [CollatzResearch.WordTrace]
  refine ⟨151254063071080383620146499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100836042047386922413430999 151254063071080383620146499)
  ·
    refine ⟨226881094606620575430219749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151254063071080383620146499 226881094606620575430219749)
    ·
      refine ⟨42540205238741357893166203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226881094606620575430219749 42540205238741357893166203)
      ·
        refine ⟨63810307858112036839749305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42540205238741357893166203 63810307858112036839749305)
        ·
          refine ⟨47857730893584027629811979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63810307858112036839749305 47857730893584027629811979)
          ·
            refine ⟨71786596340376041444717969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47857730893584027629811979 71786596340376041444717969)
            ·
              refine ⟨53839947255282031083538477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71786596340376041444717969 53839947255282031083538477)
              ·
                refine ⟨20189980220730761656326929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53839947255282031083538477 20189980220730761656326929)
                ·
                  refine ⟨15142485165548071242245197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20189980220730761656326929 15142485165548071242245197)
                  ·
                    refine ⟨5678431937080526715841949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15142485165548071242245197 5678431937080526715841949)
                    ·
                      refine ⟨2129411976405197518440731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678431937080526715841949 2129411976405197518440731)
                      ·
                        rfl

theorem cell23_4147015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_4147015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147015 prefixEnd_4147015 := by exact prefixLift 4147015
  have htrace : WordTrace (prefixWord ++ tailWord_4147015) baseStart_4147015 baseEnd_4147015 := by
    simpa [prefixWord, tailWord_4147015, baseEnd_4147015] using wordTrace_append hprefix tailTrace_4147015
  have hstable : (prefixWord ++ tailWord_4147015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147015).length < 2 ^ (prefixWord ++ tailWord_4147015).sum := by decide
  have hdescent : baseEnd_4147015 < baseStart_4147015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147016 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 2, 2, 2]
def baseStart_4147016 : Nat := 118140960795 + 4147016 * 2 ^ 59
def prefixEnd_4147016 : Nat := 4983230072969 + 3 ^ 40 * 4147016 * 2
def baseEnd_4147016 : Nat := 2129412489885852014528227

theorem tailTrace_4147016 : CollatzResearch.WordTrace tailWord_4147016 prefixEnd_4147016 2129412489885852014528227 := by
  unfold tailWord_4147016
  simp only [CollatzResearch.WordTrace]
  refine ⟨75627049772038380395466451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100836066362717840527288601 75627049772038380395466451)
  ·
    refine ⟨113440574658057570593199677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75627049772038380395466451 113440574658057570593199677)
    ·
      refine ⟨42540215496771588972449879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113440574658057570593199677 42540215496771588972449879)
      ·
        refine ⟨63810323245157383458674819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42540215496771588972449879 63810323245157383458674819)
        ·
          refine ⟨95715484867736075188012229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63810323245157383458674819 95715484867736075188012229)
          ·
            refine ⟨17946653412700514097752293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95715484867736075188012229 17946653412700514097752293)
            ·
              refine ⟨3364997514881346393328555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17946653412700514097752293 3364997514881346393328555)
              ·
                refine ⟨5047496272322019589992833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3364997514881346393328555 5047496272322019589992833)
                ·
                  refine ⟨3785622204241514692494625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047496272322019589992833 3785622204241514692494625)
                  ·
                    refine ⟨2839216653181136019370969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3785622204241514692494625 2839216653181136019370969)
                    ·
                      refine ⟨2129412489885852014528227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839216653181136019370969 2129412489885852014528227)
                      ·
                        rfl

theorem cell23_4147016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 2, 2, 2].length) (baseStart_4147016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147016 prefixEnd_4147016 := by exact prefixLift 4147016
  have htrace : WordTrace (prefixWord ++ tailWord_4147016) baseStart_4147016 baseEnd_4147016 := by
    simpa [prefixWord, tailWord_4147016, baseEnd_4147016] using wordTrace_append hprefix tailTrace_4147016
  have hstable : (prefixWord ++ tailWord_4147016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147016).length < 2 ^ (prefixWord ++ tailWord_4147016).sum := by decide
  have hdescent : baseEnd_4147016 < baseStart_4147016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147072 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 2, 4, 2]
def baseStart_4147072 : Nat := 118140960795 + 4147072 * 2 ^ 59
def prefixEnd_4147072 : Nat := 4983230072969 + 3 ^ 40 * 4147072 * 2
def baseEnd_4147072 : Nat := 2129441244802503795427969

theorem tailTrace_4147072 : CollatzResearch.WordTrace tailWord_4147072 prefixEnd_4147072 2129441244802503795427969 := by
  unfold tailWord_4147072
  simp only [CollatzResearch.WordTrace]
  refine ⟨75628071015936941177485735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100837428021249254903314313 75628071015936941177485735)
  ·
    refine ⟨113442106523905411766228603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75628071015936941177485735 113442106523905411766228603)
    ·
      refine ⟨170163159785858117649342905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113442106523905411766228603 170163159785858117649342905)
      ·
        refine ⟨127622369839393588237007179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170163159785858117649342905 127622369839393588237007179)
        ·
          refine ⟨191433554759090382355510769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127622369839393588237007179 191433554759090382355510769)
          ·
            refine ⟨143575166069317786766633077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191433554759090382355510769 143575166069317786766633077)
            ·
              refine ⟨13460171818998542509371851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143575166069317786766633077 13460171818998542509371851)
              ·
                refine ⟨20190257728497813764057777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13460171818998542509371851 20190257728497813764057777)
                ·
                  refine ⟨15142693296373360323043333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20190257728497813764057777 15142693296373360323043333)
                  ·
                    refine ⟨2839254993070005060570625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15142693296373360323043333 2839254993070005060570625)
                    ·
                      refine ⟨2129441244802503795427969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839254993070005060570625 2129441244802503795427969)
                      ·
                        rfl

theorem cell23_4147072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_4147072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147072 prefixEnd_4147072 := by exact prefixLift 4147072
  have htrace : WordTrace (prefixWord ++ tailWord_4147072) baseStart_4147072 baseEnd_4147072 := by
    simpa [prefixWord, tailWord_4147072, baseEnd_4147072] using wordTrace_append hprefix tailTrace_4147072
  have hstable : (prefixWord ++ tailWord_4147072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147072).length < 2 ^ (prefixWord ++ tailWord_4147072).sum := by decide
  have hdescent : baseEnd_4147072 < baseStart_4147072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147086 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_4147086 : Nat := 118140960795 + 4147086 * 2 ^ 59
def prefixEnd_4147086 : Nat := 4983230072969 + 3 ^ 40 * 4147086 * 2
def baseEnd_4147086 : Nat := 709816144510555580217635

theorem tailTrace_4147086 : CollatzResearch.WordTrace tailWord_4147086 prefixEnd_4147086 709816144510555580217635 := by
  unfold tailWord_4147086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18907081581727895343247639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100837768435882108497320741 18907081581727895343247639)
  ·
    refine ⟨28360622372591843014871459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18907081581727895343247639 28360622372591843014871459)
    ·
      refine ⟨42540933558887764522307189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28360622372591843014871459 42540933558887764522307189)
      ·
        refine ⟨3988212521145727923966299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42540933558887764522307189 3988212521145727923966299)
        ·
          refine ⟨5982318781718591885949449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988212521145727923966299 5982318781718591885949449)
          ·
            refine ⟨4486739086288943914462087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5982318781718591885949449 4486739086288943914462087)
            ·
              refine ⟨6730108629433415871693131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4486739086288943914462087 6730108629433415871693131)
              ·
                refine ⟨10095162944150123807539697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730108629433415871693131 10095162944150123807539697)
                ·
                  refine ⟨7571372208112592855654773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10095162944150123807539697 7571372208112592855654773)
                  ·
                    refine ⟨709816144510555580217635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7571372208112592855654773 709816144510555580217635)
                    ·
                      rfl

theorem cell23_4147086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_4147086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147086 prefixEnd_4147086 := by exact prefixLift 4147086
  have htrace : WordTrace (prefixWord ++ tailWord_4147086) baseStart_4147086 baseEnd_4147086 := by
    simpa [prefixWord, tailWord_4147086, baseEnd_4147086] using wordTrace_append hprefix tailTrace_4147086
  have hstable : (prefixWord ++ tailWord_4147086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147086).length < 2 ^ (prefixWord ++ tailWord_4147086).sum := by decide
  have hdescent : baseEnd_4147086 < baseStart_4147086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147172 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_4147172 : Nat := 118140960795 + 4147172 * 2 ^ 59
def prefixEnd_4147172 : Nat := 4983230072969 + 3 ^ 40 * 4147172 * 2
def baseEnd_4147172 : Nat := 709830864289317801392503

theorem tailTrace_4147172 : CollatzResearch.WordTrace tailWord_4147172 prefixEnd_4147172 709830864289317801392503 := by
  unfold tailWord_4147172
  simp only [CollatzResearch.WordTrace]
  refine ⟨75629894665755799716805885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100839859554341066289074513 75629894665755799716805885)
  ·
    refine ⟨28361210499658424893802207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75629894665755799716805885 28361210499658424893802207)
    ·
      refine ⟨42541815749487637340703311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28361210499658424893802207 42541815749487637340703311)
      ·
        refine ⟨63812723624231456011054967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42541815749487637340703311 63812723624231456011054967)
        ·
          refine ⟨95719085436347184016582451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63812723624231456011054967 95719085436347184016582451)
          ·
            refine ⟨143578628154520776024873677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95719085436347184016582451 143578628154520776024873677)
            ·
              refine ⟨53841985557945291009327629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143578628154520776024873677 53841985557945291009327629)
              ·
                refine ⟨20190744584229484128497861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53841985557945291009327629 20190744584229484128497861)
                ·
                  refine ⟨3785764609543028274093349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20190744584229484128497861 3785764609543028274093349)
                  ·
                    refine ⟨709830864289317801392503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785764609543028274093349 709830864289317801392503)
                    ·
                      rfl

theorem cell23_4147172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_4147172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147172 prefixEnd_4147172 := by exact prefixLift 4147172
  have htrace : WordTrace (prefixWord ++ tailWord_4147172) baseStart_4147172 baseEnd_4147172 := by
    simpa [prefixWord, tailWord_4147172, baseEnd_4147172] using wordTrace_append hprefix tailTrace_4147172
  have hstable : (prefixWord ++ tailWord_4147172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147172).length < 2 ^ (prefixWord ++ tailWord_4147172).sum := by decide
  have hdescent : baseEnd_4147172 < baseStart_4147172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147236 : List Nat := [2, 3, 1, 4, 3, 1, 1, 8]
def baseStart_4147236 : Nat := 118140960795 + 4147236 * 2 ^ 59
def prefixEnd_4147236 : Nat := 4983230072969 + 3 ^ 40 * 4147236 * 2
def baseEnd_4147236 : Nat := 78871313171475598288045

theorem tailTrace_4147236 : CollatzResearch.WordTrace tailWord_4147236 prefixEnd_4147236 78871313171475598288045 := by
  unfold tailWord_4147236
  simp only [CollatzResearch.WordTrace]
  refine ⟨75631061801639869181970781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100841415735519825575961041 75631061801639869181970781)
  ·
    refine ⟨28361648175614950943239043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75631061801639869181970781 28361648175614950943239043)
    ·
      refine ⟨42542472263422426414858565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28361648175614950943239043 42542472263422426414858565)
      ·
        refine ⟨7976713549391704952785981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42542472263422426414858565 7976713549391704952785981)
        ·
          refine ⟨2991267581021889357294743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7976713549391704952785981 2991267581021889357294743)
          ·
            refine ⟨4486901371532834035942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991267581021889357294743 4486901371532834035942115)
            ·
              refine ⟨6730352057299251053913173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4486901371532834035942115 6730352057299251053913173)
              ·
                refine ⟨78871313171475598288045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6730352057299251053913173 78871313171475598288045)
                ·
                  rfl

theorem cell23_4147236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 8].length) (baseStart_4147236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147236 prefixEnd_4147236 := by exact prefixLift 4147236
  have htrace : WordTrace (prefixWord ++ tailWord_4147236) baseStart_4147236 baseEnd_4147236 := by
    simpa [prefixWord, tailWord_4147236, baseEnd_4147236] using wordTrace_append hprefix tailTrace_4147236
  have hstable : (prefixWord ++ tailWord_4147236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147236).length < 2 ^ (prefixWord ++ tailWord_4147236).sum := by decide
  have hdescent : baseEnd_4147236 < baseStart_4147236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147246 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_4147246 : Nat := 118140960795 + 4147246 * 2 ^ 59
def prefixEnd_4147246 : Nat := 4983230072969 + 3 ^ 40 * 4147246 * 2
def baseEnd_4147246 : Nat := 2129530590436386114652169

theorem tailTrace_4147246 : CollatzResearch.WordTrace tailWord_4147246 prefixEnd_4147246 2129530590436386114652169 := by
  unfold tailWord_4147246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18907811041655438758975699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100841658888829006714537061 18907811041655438758975699)
  ·
    refine ⟨28361716562483158138463549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18907811041655438758975699 28361716562483158138463549)
    ·
      refine ⟨10635643710931184301923831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28361716562483158138463549 10635643710931184301923831)
      ·
        refine ⟨15953465566396776452885747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635643710931184301923831 15953465566396776452885747)
        ·
          refine ⟨23930198349595164679328621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15953465566396776452885747 23930198349595164679328621)
          ·
            refine ⟨8973824381098186754748233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23930198349595164679328621 8973824381098186754748233)
            ·
              refine ⟨6730368285823640066061175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8973824381098186754748233 6730368285823640066061175)
              ·
                refine ⟨10095552428735460099091763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730368285823640066061175 10095552428735460099091763)
                ·
                  refine ⟨15143328643103190148637645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10095552428735460099091763 15143328643103190148637645)
                  ·
                    refine ⟨5678748241163696305739117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15143328643103190148637645 5678748241163696305739117)
                    ·
                      refine ⟨2129530590436386114652169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678748241163696305739117 2129530590436386114652169)
                      ·
                        rfl

theorem cell23_4147246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_4147246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147246 prefixEnd_4147246 := by exact prefixLift 4147246
  have htrace : WordTrace (prefixWord ++ tailWord_4147246) baseStart_4147246 baseEnd_4147246 := by
    simpa [prefixWord, tailWord_4147246, baseEnd_4147246] using wordTrace_append hprefix tailTrace_4147246
  have hstable : (prefixWord ++ tailWord_4147246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147246).length < 2 ^ (prefixWord ++ tailWord_4147246).sum := by decide
  have hdescent : baseEnd_4147246 < baseStart_4147246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147272 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 1, 6, 3]
def baseStart_4147272 : Nat := 118140960795 + 4147272 * 2 ^ 59
def prefixEnd_4147272 : Nat := 4983230072969 + 3 ^ 40 * 4147272 * 2
def baseEnd_4147272 : Nat := 2129543940933403012927049

theorem tailTrace_4147272 : CollatzResearch.WordTrace tailWord_4147272 prefixEnd_4147272 2129543940933403012927049 := by
  unfold tailWord_4147272
  simp only [CollatzResearch.WordTrace]
  refine ⟨75631718315574658256126035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100842291087432877674834713 75631718315574658256126035)
  ·
    refine ⟨113447577473361987384189053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75631718315574658256126035 113447577473361987384189053)
    ·
      refine ⟨42542841552510745269070895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113447577473361987384189053 42542841552510745269070895)
      ·
        refine ⟨63814262328766117903606343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42542841552510745269070895 63814262328766117903606343)
        ·
          refine ⟨95721393493149176855409515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63814262328766117903606343 95721393493149176855409515)
          ·
            refine ⟨143582090239723765283114273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95721393493149176855409515 143582090239723765283114273)
            ·
              refine ⟨107686567679792823962335705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143582090239723765283114273 107686567679792823962335705)
              ·
                refine ⟨80764925759844617971751779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107686567679792823962335705 80764925759844617971751779)
                ·
                  refine ⟨121147388639766926957627669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80764925759844617971751779 121147388639766926957627669)
                  ·
                    refine ⟨5678783842489074701138797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121147388639766926957627669 5678783842489074701138797)
                    ·
                      refine ⟨2129543940933403012927049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5678783842489074701138797 2129543940933403012927049)
                      ·
                        rfl

theorem cell23_4147272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_4147272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147272 prefixEnd_4147272 := by exact prefixLift 4147272
  have htrace : WordTrace (prefixWord ++ tailWord_4147272) baseStart_4147272 baseEnd_4147272 := by
    simpa [prefixWord, tailWord_4147272, baseEnd_4147272] using wordTrace_append hprefix tailTrace_4147272
  have hstable : (prefixWord ++ tailWord_4147272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147272).length < 2 ^ (prefixWord ++ tailWord_4147272).sum := by decide
  have hdescent : baseEnd_4147272 < baseStart_4147272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147322 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_4147322 : Nat := 118140960795 + 4147322 * 2 ^ 59
def prefixEnd_4147322 : Nat := 4983230072969 + 3 ^ 40 * 4147322 * 2
def baseEnd_4147322 : Nat := 709856538322042605767273

theorem tailTrace_4147322 : CollatzResearch.WordTrace tailWord_4147322 prefixEnd_4147322 709856538322042605767273 := by
  unfold tailWord_4147322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37816315070242043762893055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100843506853978783367714813 37816315070242043762893055)
  ·
    refine ⟨56724472605363065644339583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37816315070242043762893055 56724472605363065644339583)
    ·
      refine ⟨85086708908044598466509375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56724472605363065644339583 85086708908044598466509375)
      ·
        refine ⟨127630063362066897699764063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85086708908044598466509375 127630063362066897699764063)
        ·
          refine ⟨191445095043100346549646095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127630063362066897699764063 191445095043100346549646095)
          ·
            refine ⟨287167642564650519824469143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191445095043100346549646095 287167642564650519824469143)
            ·
              refine ⟨430751463846975779736703715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287167642564650519824469143 430751463846975779736703715)
              ·
                refine ⟨646127195770463669605055573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430751463846975779736703715 646127195770463669605055573)
                ·
                  refine ⟨7571803075435121128184245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 646127195770463669605055573 7571803075435121128184245)
                  ·
                    refine ⟨709856538322042605767273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7571803075435121128184245 709856538322042605767273)
                    ·
                      rfl

theorem cell23_4147322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_4147322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147322 prefixEnd_4147322 := by exact prefixLift 4147322
  have htrace : WordTrace (prefixWord ++ tailWord_4147322) baseStart_4147322 baseEnd_4147322 := by
    simpa [prefixWord, tailWord_4147322, baseEnd_4147322] using wordTrace_append hprefix tailTrace_4147322
  have hstable : (prefixWord ++ tailWord_4147322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147322).length < 2 ^ (prefixWord ++ tailWord_4147322).sum := by decide
  have hdescent : baseEnd_4147322 < baseStart_4147322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147346 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_4147346 : Nat := 118140960795 + 4147346 * 2 ^ 59
def prefixEnd_4147346 : Nat := 4983230072969 + 3 ^ 40 * 4147346 * 2
def baseEnd_4147346 : Nat := 2129581938501835723401709

theorem tailTrace_4147346 : CollatzResearch.WordTrace tailWord_4147346 prefixEnd_4147346 2129581938501835723401709 := by
  unfold tailWord_4147346
  simp only [CollatzResearch.WordTrace]
  refine ⟨37816533908220306787611473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100844090421920818100297261 37816533908220306787611473)
  ·
    refine ⟨28362400431165230090708605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37816533908220306787611473 28362400431165230090708605)
    ·
      refine ⟨10635900161686961284015727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28362400431165230090708605 10635900161686961284015727)
      ·
        refine ⟨15953850242530441926023591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10635900161686961284015727 15953850242530441926023591)
        ·
          refine ⟨23930775363795662889035387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15953850242530441926023591 23930775363795662889035387)
          ·
            refine ⟨35896163045693494333553081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23930775363795662889035387 35896163045693494333553081)
            ·
              refine ⟨26922122284270120750164811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35896163045693494333553081 26922122284270120750164811)
              ·
                refine ⟨40383183426405181125247217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26922122284270120750164811 40383183426405181125247217)
                ·
                  refine ⟨30287387569803885843935413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40383183426405181125247217 30287387569803885843935413)
                  ·
                    refine ⟨2839442584669114297868945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30287387569803885843935413 2839442584669114297868945)
                    ·
                      refine ⟨2129581938501835723401709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839442584669114297868945 2129581938501835723401709)
                      ·
                        rfl

theorem cell23_4147346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_4147346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147346 prefixEnd_4147346 := by exact prefixLift 4147346
  have htrace : WordTrace (prefixWord ++ tailWord_4147346) baseStart_4147346 baseEnd_4147346 := by
    simpa [prefixWord, tailWord_4147346, baseEnd_4147346] using wordTrace_append hprefix tailTrace_4147346
  have hstable : (prefixWord ++ tailWord_4147346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147346).length < 2 ^ (prefixWord ++ tailWord_4147346).sum := by decide
  have hdescent : baseEnd_4147346 < baseStart_4147346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147354 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4147354 : Nat := 118140960795 + 4147354 * 2 ^ 59
def prefixEnd_4147354 : Nat := 4983230072969 + 3 ^ 40 * 4147354 * 2
def baseEnd_4147354 : Nat := 2129586046347071692101673

theorem tailTrace_4147354 : CollatzResearch.WordTrace tailWord_4147354 prefixEnd_4147354 2129586046347071692101673 := by
  unfold tailWord_4147354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37816606854213061129184279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100844284944568163011158077 37816606854213061129184279)
  ·
    refine ⟨56724910281319591693776419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37816606854213061129184279 56724910281319591693776419)
    ·
      refine ⟨85087365421979387540664629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56724910281319591693776419 85087365421979387540664629)
      ·
        refine ⟨7976940508310567581937309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85087365421979387540664629 7976940508310567581937309)
        ·
          refine ⟨2991352690616462843226491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7976940508310567581937309 2991352690616462843226491)
          ·
            refine ⟨4487029035924694264839737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2991352690616462843226491 4487029035924694264839737)
            ·
              refine ⟨3365271776943520698629803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487029035924694264839737 3365271776943520698629803)
              ·
                refine ⟨5047907665415281047944705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365271776943520698629803 5047907665415281047944705)
                ·
                  refine ⟨3785930749061460785958529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5047907665415281047944705 3785930749061460785958529)
                  ·
                    refine ⟨2839448061796095589468897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3785930749061460785958529 2839448061796095589468897)
                    ·
                      refine ⟨2129586046347071692101673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839448061796095589468897 2129586046347071692101673)
                      ·
                        rfl

theorem cell23_4147354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4147354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147354 prefixEnd_4147354 := by exact prefixLift 4147354
  have htrace : WordTrace (prefixWord ++ tailWord_4147354) baseStart_4147354 baseEnd_4147354 := by
    simpa [prefixWord, tailWord_4147354, baseEnd_4147354] using wordTrace_append hprefix tailTrace_4147354
  have hstable : (prefixWord ++ tailWord_4147354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147354).length < 2 ^ (prefixWord ++ tailWord_4147354).sum := by decide
  have hdescent : baseEnd_4147354 < baseStart_4147354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147420 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4147420 : Nat := 118140960795 + 4147420 * 2 ^ 59
def prefixEnd_4147420 : Nat := 4983230072969 + 3 ^ 40 * 4147420 * 2
def baseEnd_4147420 : Nat := 709873312023422811292123

theorem tailTrace_4147420 : CollatzResearch.WordTrace tailWord_4147420 prefixEnd_4147420 709873312023422811292123 := by
  unfold tailWord_4147420
  simp only [CollatzResearch.WordTrace]
  refine ⟨75634417317306568894319857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100845889756408758525759809 75634417317306568894319857)
  ·
    refine ⟨56725812987979926670739893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75634417317306568894319857 56725812987979926670739893)
    ·
      refine ⟨5318044967623118125381865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56725812987979926670739893 5318044967623118125381865)
      ·
        refine ⟨3988533725717338594036399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5318044967623118125381865 3988533725717338594036399)
        ·
          refine ⟨5982800588576007891054599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988533725717338594036399 5982800588576007891054599)
          ·
            refine ⟨8974200882864011836581899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982800588576007891054599 8974200882864011836581899)
            ·
              refine ⟨13461301324296017754872849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974200882864011836581899 13461301324296017754872849)
              ·
                refine ⟨10095975993222013316154637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13461301324296017754872849 10095975993222013316154637)
                ·
                  refine ⟨3785990997458254993557989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10095975993222013316154637 3785990997458254993557989)
                  ·
                    refine ⟨709873312023422811292123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3785990997458254993557989 709873312023422811292123)
                    ·
                      rfl

theorem cell23_4147420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4147420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147420 prefixEnd_4147420 := by exact prefixLift 4147420
  have htrace : WordTrace (prefixWord ++ tailWord_4147420) baseStart_4147420 baseEnd_4147420 := by
    simpa [prefixWord, tailWord_4147420, baseEnd_4147420] using wordTrace_append hprefix tailTrace_4147420
  have hstable : (prefixWord ++ tailWord_4147420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147420).length < 2 ^ (prefixWord ++ tailWord_4147420).sum := by decide
  have hdescent : baseEnd_4147420 < baseStart_4147420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147436 : List Nat := [2, 2, 1, 1, 2, 3, 3, 1, 1, 5, 2]
def baseStart_4147436 : Nat := 118140960795 + 4147436 * 2 ^ 59
def prefixEnd_4147436 : Nat := 4983230072969 + 3 ^ 40 * 4147436 * 2
def baseEnd_4147436 : Nat := 2129628151760740371276295

theorem tailTrace_4147436 : CollatzResearch.WordTrace tailWord_4147436 prefixEnd_4147436 2129628151760740371276295 := by
  unfold tailWord_4147436
  simp only [CollatzResearch.WordTrace]
  refine ⟨75634709101277586260611081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100846278801703448347481441 75634709101277586260611081)
  ·
    refine ⟨56726031825958189695458311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75634709101277586260611081 56726031825958189695458311)
    ·
      refine ⟨85089047738937284543187467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56726031825958189695458311 85089047738937284543187467)
      ·
        refine ⟨127633571608405926814781201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85089047738937284543187467 127633571608405926814781201)
        ·
          refine ⟨95725178706304445111085901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127633571608405926814781201 95725178706304445111085901)
          ·
            refine ⟨35896942014864166916657213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95725178706304445111085901 35896942014864166916657213)
            ·
              refine ⟨13461353255574062593746455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35896942014864166916657213 13461353255574062593746455)
              ·
                refine ⟨20192029883361093890619683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13461353255574062593746455 20192029883361093890619683)
                ·
                  refine ⟨30288044825041640835929525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20192029883361093890619683 30288044825041640835929525)
                  ·
                    refine ⟨2839504202347653828368393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30288044825041640835929525 2839504202347653828368393)
                    ·
                      refine ⟨2129628151760740371276295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839504202347653828368393 2129628151760740371276295)
                      ·
                        rfl

theorem cell23_4147436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 5, 2].length) (baseStart_4147436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147436 prefixEnd_4147436 := by exact prefixLift 4147436
  have htrace : WordTrace (prefixWord ++ tailWord_4147436) baseStart_4147436 baseEnd_4147436 := by
    simpa [prefixWord, tailWord_4147436, baseEnd_4147436] using wordTrace_append hprefix tailTrace_4147436
  have hstable : (prefixWord ++ tailWord_4147436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147436).length < 2 ^ (prefixWord ++ tailWord_4147436).sum := by decide
  have hdescent : baseEnd_4147436 < baseStart_4147436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147449 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_4147449 : Nat := 118140960795 + 4147449 * 2 ^ 59
def prefixEnd_4147449 : Nat := 4983230072969 + 3 ^ 40 * 4147449 * 2
def baseEnd_4147449 : Nat := 2129634827009248820413735

theorem tailTrace_4147449 : CollatzResearch.WordTrace tailWord_4147449 prefixEnd_4147449 2129634827009248820413735 := by
  unfold tailWord_4147449
  simp only [CollatzResearch.WordTrace]
  refine ⟨151269892351508075741445401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100846594901005383827630267 151269892351508075741445401)
  ·
    refine ⟨113452419263631056806084051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151269892351508075741445401 113452419263631056806084051)
    ·
      refine ⟨170178628895446585209126077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113452419263631056806084051 170178628895446585209126077)
      ·
        refine ⟨63816985835792469453422279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170178628895446585209126077 63816985835792469453422279)
        ·
          refine ⟨95725478753688704180133419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63816985835792469453422279 95725478753688704180133419)
          ·
            refine ⟨143588218130533056270200129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95725478753688704180133419 143588218130533056270200129)
            ·
              refine ⟨107691163597899792202650097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143588218130533056270200129 107691163597899792202650097)
              ·
                refine ⟨80768372698424844151987573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107691163597899792202650097 80768372698424844151987573)
                ·
                  refine ⟨7572034940477329139248835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80768372698424844151987573 7572034940477329139248835)
                  ·
                    refine ⟨11358052410715993708873253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7572034940477329139248835 11358052410715993708873253)
                    ·
                      refine ⟨2129634827009248820413735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11358052410715993708873253 2129634827009248820413735)
                      ·
                        rfl

theorem cell23_4147449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_4147449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147449 prefixEnd_4147449 := by exact prefixLift 4147449
  have htrace : WordTrace (prefixWord ++ tailWord_4147449) baseStart_4147449 baseEnd_4147449 := by
    simpa [prefixWord, tailWord_4147449, baseEnd_4147449] using wordTrace_append hprefix tailTrace_4147449
  have hstable : (prefixWord ++ tailWord_4147449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147449).length < 2 ^ (prefixWord ++ tailWord_4147449).sum := by decide
  have hdescent : baseEnd_4147449 < baseStart_4147449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147460 : List Nat := [2, 3, 2, 2, 3, 1, 2, 1, 3, 1, 3]
def baseStart_4147460 : Nat := 118140960795 + 4147460 * 2 ^ 59
def prefixEnd_4147460 : Nat := 4983230072969 + 3 ^ 40 * 4147460 * 2
def baseEnd_4147460 : Nat := 2129640475296448277376185

theorem tailTrace_4147460 : CollatzResearch.WordTrace tailWord_4147460 prefixEnd_4147460 2129640475296448277376185 := by
  unfold tailWord_4147460
  simp only [CollatzResearch.WordTrace]
  refine ⟨75635146777234112310047917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100846862369645483080063889 75635146777234112310047917)
  ·
    refine ⟨28363180041462792116267969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75635146777234112310047917 28363180041462792116267969)
    ·
      refine ⟨21272385031097094087200977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28363180041462792116267969 21272385031097094087200977)
      ·
        refine ⟨15954288773322820565400733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21272385031097094087200977 15954288773322820565400733)
        ·
          refine ⟨5982858289996057712025275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15954288773322820565400733 5982858289996057712025275)
          ·
            refine ⟨8974287434994086568037913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5982858289996057712025275 8974287434994086568037913)
            ·
              refine ⟨6730715576245564926028435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8974287434994086568037913 6730715576245564926028435)
              ·
                refine ⟨10096073364368347389042653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6730715576245564926028435 10096073364368347389042653)
                ·
                  refine ⟨3786027511638130270890995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10096073364368347389042653 3786027511638130270890995)
                  ·
                    refine ⟨5679041267457195406336493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3786027511638130270890995 5679041267457195406336493)
                    ·
                      refine ⟨2129640475296448277376185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5679041267457195406336493 2129640475296448277376185)
                      ·
                        rfl

theorem cell23_4147460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_4147460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147460 prefixEnd_4147460 := by exact prefixLift 4147460
  have htrace : WordTrace (prefixWord ++ tailWord_4147460) baseStart_4147460 baseEnd_4147460 := by
    simpa [prefixWord, tailWord_4147460, baseEnd_4147460] using wordTrace_append hprefix tailTrace_4147460
  have hstable : (prefixWord ++ tailWord_4147460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147460).length < 2 ^ (prefixWord ++ tailWord_4147460).sum := by decide
  have hdescent : baseEnd_4147460 < baseStart_4147460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147483 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 3, 2, 2]
def baseStart_4147483 : Nat := 118140960795 + 4147483 * 2 ^ 59
def prefixEnd_4147483 : Nat := 4983230072969 + 3 ^ 40 * 4147483 * 2
def baseEnd_4147483 : Nat := 2129652285351501687388579

theorem tailTrace_4147483 : CollatzResearch.WordTrace tailWord_4147483 prefixEnd_4147483 2129652285351501687388579 := by
  unfold tailWord_4147483
  simp only [CollatzResearch.WordTrace]
  refine ⟨151271132433384899548183103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100847421622256599698788735 151271132433384899548183103)
  ·
    refine ⟨226906698650077349322274655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151271132433384899548183103 226906698650077349322274655)
    ·
      refine ⟨340360047975116023983411983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226906698650077349322274655 340360047975116023983411983)
      ·
        refine ⟨510540071962674035975117975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340360047975116023983411983 510540071962674035975117975)
        ·
          refine ⟨765810107944011053962676963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510540071962674035975117975 765810107944011053962676963)
          ·
            refine ⟨1148715161916016580944015445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765810107944011053962676963 1148715161916016580944015445)
            ·
              refine ⟨13461505803703319307937681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1148715161916016580944015445 13461505803703319307937681)
              ·
                refine ⟨10096129352777489480953261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13461505803703319307937681 10096129352777489480953261)
                ·
                  refine ⟨3786048507291558555357473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10096129352777489480953261 3786048507291558555357473)
                  ·
                    refine ⟨2839536380468668916518105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3786048507291558555357473 2839536380468668916518105)
                    ·
                      refine ⟨2129652285351501687388579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839536380468668916518105 2129652285351501687388579)
                      ·
                        rfl

theorem cell23_4147483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 3, 2, 2].length) (baseStart_4147483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147483 prefixEnd_4147483 := by exact prefixLift 4147483
  have htrace : WordTrace (prefixWord ++ tailWord_4147483) baseStart_4147483 baseEnd_4147483 := by
    simpa [prefixWord, tailWord_4147483, baseEnd_4147483] using wordTrace_append hprefix tailTrace_4147483
  have hstable : (prefixWord ++ tailWord_4147483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147483).length < 2 ^ (prefixWord ++ tailWord_4147483).sum := by decide
  have hdescent : baseEnd_4147483 < baseStart_4147483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147506 : List Nat := [3, 2, 1, 1, 5, 2, 9]
def baseStart_4147506 : Nat := 118140960795 + 4147506 * 2 ^ 59
def prefixEnd_4147506 : Nat := 4983230072969 + 3 ^ 40 * 4147506 * 2
def baseEnd_4147506 : Nat := 26292149326006853054333

theorem tailTrace_4147506 : CollatzResearch.WordTrace tailWord_4147506 prefixEnd_4147506 26292149326006853054333 := by
  unfold tailWord_4147506
  simp only [CollatzResearch.WordTrace]
  refine ⟨37817992828075393619067593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100847980874867716317513581 37817992828075393619067593)
  ·
    refine ⟨28363494621056545214300695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37817992828075393619067593 28363494621056545214300695)
    ·
      refine ⟨42545241931584817821451043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28363494621056545214300695 42545241931584817821451043)
      ·
        refine ⟨63817862897377226732176565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42545241931584817821451043 63817862897377226732176565)
        ·
          refine ⟨5982924646629115006141553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63817862897377226732176565 5982924646629115006141553)
          ·
            refine ⟨4487193484971836254606165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5982924646629115006141553 4487193484971836254606165)
            ·
              refine ⟨26292149326006853054333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4487193484971836254606165 26292149326006853054333)
              ·
                rfl

theorem cell23_4147506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 9].length) (baseStart_4147506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147506 prefixEnd_4147506 := by exact prefixLift 4147506
  have htrace : WordTrace (prefixWord ++ tailWord_4147506) baseStart_4147506 baseEnd_4147506 := by
    simpa [prefixWord, tailWord_4147506, baseEnd_4147506] using wordTrace_append hprefix tailTrace_4147506
  have hstable : (prefixWord ++ tailWord_4147506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147506).length < 2 ^ (prefixWord ++ tailWord_4147506).sum := by decide
  have hdescent : baseEnd_4147506 < baseStart_4147506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147519 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 2, 7]
def baseStart_4147519 : Nat := 118140960795 + 4147519 * 2 ^ 59
def prefixEnd_4147519 : Nat := 4983230072969 + 3 ^ 40 * 4147519 * 2
def baseEnd_4147519 : Nat := 709890256885021182179471

theorem tailTrace_4147519 : CollatzResearch.WordTrace tailWord_4147519 prefixEnd_4147519 709890256885021182179471 := by
  unfold tailWord_4147519
  simp only [CollatzResearch.WordTrace]
  refine ⟨151272445461254477696493611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100848296974169651797662407 151272445461254477696493611)
  ·
    refine ⟨226908668191881716544740417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151272445461254477696493611 226908668191881716544740417)
    ·
      refine ⟨170181501143911287408555313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226908668191881716544740417 170181501143911287408555313)
      ·
        refine ⟨127636125857933465556416485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170181501143911287408555313 127636125857933465556416485)
        ·
          refine ⟨23931773598362524791828091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127636125857933465556416485 23931773598362524791828091)
          ·
            refine ⟨35897660397543787187742137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23931773598362524791828091 35897660397543787187742137)
            ·
              refine ⟨26923245298157840390806603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35897660397543787187742137 26923245298157840390806603)
              ·
                refine ⟨40384867947236760586209905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26923245298157840390806603 40384867947236760586209905)
                ·
                  refine ⟨30288650960427570439657429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40384867947236760586209905 30288650960427570439657429)
                  ·
                    refine ⟨709890256885021182179471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30288650960427570439657429 709890256885021182179471)
                    ·
                      rfl

theorem cell23_4147519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_4147519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147519 prefixEnd_4147519 := by exact prefixLift 4147519
  have htrace : WordTrace (prefixWord ++ tailWord_4147519) baseStart_4147519 baseEnd_4147519 := by
    simpa [prefixWord, tailWord_4147519, baseEnd_4147519] using wordTrace_append hprefix tailTrace_4147519
  have hstable : (prefixWord ++ tailWord_4147519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147519).length < 2 ^ (prefixWord ++ tailWord_4147519).sum := by decide
  have hdescent : baseEnd_4147519 < baseStart_4147519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147539 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4]
def baseStart_4147539 : Nat := 118140960795 + 4147539 * 2 ^ 59
def prefixEnd_4147539 : Nat := 4983230072969 + 3 ^ 40 * 4147539 * 2
def baseEnd_4147539 : Nat := 2129681040268153468288321

theorem tailTrace_4147539 : CollatzResearch.WordTrace tailWord_4147539 prefixEnd_4147539 2129681040268153468288321 := by
  unfold tailWord_4147539
  simp only [CollatzResearch.WordTrace]
  refine ⟨151273174921182021112221671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100848783280788014074814447 151273174921182021112221671)
  ·
    refine ⟨226909762381773031668332507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151273174921182021112221671 226909762381773031668332507)
    ·
      refine ⟨340364643572659547502498761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226909762381773031668332507 340364643572659547502498761)
      ·
        refine ⟨255273482679494660626874071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340364643572659547502498761 255273482679494660626874071)
        ·
          refine ⟨382910224019241990940311107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255273482679494660626874071 382910224019241990940311107)
          ·
            refine ⟨574365336028862986410466661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382910224019241990940311107 574365336028862986410466661)
            ·
              refine ⟨107693500505411809951962499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 574365336028862986410466661 107693500505411809951962499)
              ·
                refine ⟨161540250758117714927943749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107693500505411809951962499 161540250758117714927943749)
                ·
                  refine ⟨30288797017147071548989453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161540250758117714927943749 30288797017147071548989453)
                  ·
                    refine ⟨11358298881430151830871045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30288797017147071548989453 11358298881430151830871045)
                    ·
                      refine ⟨2129681040268153468288321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11358298881430151830871045 2129681040268153468288321)
                      ·
                        rfl

theorem cell23_4147539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_4147539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147539 prefixEnd_4147539 := by exact prefixLift 4147539
  have htrace : WordTrace (prefixWord ++ tailWord_4147539) baseStart_4147539 baseEnd_4147539 := by
    simpa [prefixWord, tailWord_4147539, baseEnd_4147539] using wordTrace_append hprefix tailTrace_4147539
  have hstable : (prefixWord ++ tailWord_4147539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147539).length < 2 ^ (prefixWord ++ tailWord_4147539).sum := by decide
  have hdescent : baseEnd_4147539 < baseStart_4147539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147543 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 3, 3, 2]
def baseStart_4147543 : Nat := 118140960795 + 4147543 * 2 ^ 59
def prefixEnd_4147543 : Nat := 4983230072969 + 3 ^ 40 * 4147543 * 2
def baseEnd_4147543 : Nat := 2129683094190771452638303

theorem tailTrace_4147543 : CollatzResearch.WordTrace tailWord_4147543 prefixEnd_4147543 2129683094190771452638303 := by
  unfold tailWord_4147543
  simp only [CollatzResearch.WordTrace]
  refine ⟨151273320813167529795367283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100848880542111686530244855 151273320813167529795367283)
  ·
    refine ⟨226909981219751294693050925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151273320813167529795367283 226909981219751294693050925)
    ·
      refine ⟨85091242957406735509894097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226909981219751294693050925 85091242957406735509894097)
      ·
        refine ⟨63818432218055051632420573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85091242957406735509894097 63818432218055051632420573)
        ·
          refine ⟨23931912081770644362157715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63818432218055051632420573 23931912081770644362157715)
          ·
            refine ⟨35897868122655966543236573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23931912081770644362157715 35897868122655966543236573)
            ·
              refine ⟨13461700545995987453713715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35897868122655966543236573 13461700545995987453713715)
              ·
                refine ⟨20192550818993981180570573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13461700545995987453713715 20192550818993981180570573)
                ·
                  refine ⟨7572206557122742942713965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20192550818993981180570573 7572206557122742942713965)
                  ·
                    refine ⟨2839577458921028603517737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7572206557122742942713965 2839577458921028603517737)
                    ·
                      refine ⟨2129683094190771452638303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839577458921028603517737 2129683094190771452638303)
                      ·
                        rfl

theorem cell23_4147543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_4147543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147543 prefixEnd_4147543 := by exact prefixLift 4147543
  have htrace : WordTrace (prefixWord ++ tailWord_4147543) baseStart_4147543 baseEnd_4147543 := by
    simpa [prefixWord, tailWord_4147543, baseEnd_4147543] using wordTrace_append hprefix tailTrace_4147543
  have hstable : (prefixWord ++ tailWord_4147543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147543).length < 2 ^ (prefixWord ++ tailWord_4147543).sum := by decide
  have hdescent : baseEnd_4147543 < baseStart_4147543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147569 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_4147569 : Nat := 118140960795 + 4147569 * 2 ^ 59
def prefixEnd_4147569 : Nat := 4983230072969 + 3 ^ 40 * 4147569 * 2
def baseEnd_4147569 : Nat := 2129696444687788350913183

theorem tailTrace_4147569 : CollatzResearch.WordTrace tailWord_4147569 prefixEnd_4147569 2129696444687788350913183 := by
  unfold tailWord_4147569
  simp only [CollatzResearch.WordTrace]
  refine ⟨151274269111073336235813761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100849512740715557490542507 151274269111073336235813761)
  ·
    refine ⟨113455701833305002176860321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151274269111073336235813761 113455701833305002176860321)
    ·
      refine ⟨85091776374978751632645241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113455701833305002176860321 85091776374978751632645241)
      ·
        refine ⟨63818832281234063724483931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85091776374978751632645241 63818832281234063724483931)
        ·
          refine ⟨95728248421851095586725897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63818832281234063724483931 95728248421851095586725897)
          ·
            refine ⟨71796186316388321690044423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95728248421851095586725897 71796186316388321690044423)
            ·
              refine ⟨107694279474582482535066635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71796186316388321690044423 107694279474582482535066635)
              ·
                refine ⟨161541419211873723802599953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107694279474582482535066635 161541419211873723802599953)
                ·
                  refine ⟨121156064408905292851949965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161541419211873723802599953 121156064408905292851949965)
                  ·
                    refine ⟨45433524153339484819481237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121156064408905292851949965 45433524153339484819481237)
                    ·
                      refine ⟨2129696444687788350913183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45433524153339484819481237 2129696444687788350913183)
                      ·
                        rfl

theorem cell23_4147569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_4147569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147569 prefixEnd_4147569 := by exact prefixLift 4147569
  have htrace : WordTrace (prefixWord ++ tailWord_4147569) baseStart_4147569 baseEnd_4147569 := by
    simpa [prefixWord, tailWord_4147569, baseEnd_4147569] using wordTrace_append hprefix tailTrace_4147569
  have hstable : (prefixWord ++ tailWord_4147569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147569).length < 2 ^ (prefixWord ++ tailWord_4147569).sum := by decide
  have hdescent : baseEnd_4147569 < baseStart_4147569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147596 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 7]
def baseStart_4147596 : Nat := 118140960795 + 4147596 * 2 ^ 59
def prefixEnd_4147596 : Nat := 4983230072969 + 3 ^ 40 * 4147596 * 2
def baseEnd_4147596 : Nat := 236634478740606638363951

theorem tailTrace_4147596 : CollatzResearch.WordTrace tailWord_4147596 prefixEnd_4147596 236634478740606638363951 := by
  unfold tailWord_4147596
  simp only [CollatzResearch.WordTrace]
  refine ⟨75637626940987759923523321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100850169254650346564697761 75637626940987759923523321)
  ·
    refine ⟨56728220205740819942642491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75637626940987759923523321 56728220205740819942642491)
    ·
      refine ⟨85092330308611229913963737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56728220205740819942642491 85092330308611229913963737)
      ·
        refine ⟨63819247731458422435472803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85092330308611229913963737 63819247731458422435472803)
        ·
          refine ⟨95728871597187633653209205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63819247731458422435472803 95728871597187633653209205)
          ·
            refine ⟨8974581712236340654988363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95728871597187633653209205 8974581712236340654988363)
            ·
              refine ⟨13461872568354510982482545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974581712236340654988363 13461872568354510982482545)
              ·
                refine ⟨10096404426265883236861909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13461872568354510982482545 10096404426265883236861909)
                ·
                  refine ⟨236634478740606638363951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10096404426265883236861909 236634478740606638363951)
                  ·
                    rfl

theorem cell23_4147596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_4147596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147596 prefixEnd_4147596 := by exact prefixLift 4147596
  have htrace : WordTrace (prefixWord ++ tailWord_4147596) baseStart_4147596 baseEnd_4147596 := by
    simpa [prefixWord, tailWord_4147596, baseEnd_4147596] using wordTrace_append hprefix tailTrace_4147596
  have hstable : (prefixWord ++ tailWord_4147596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147596).length < 2 ^ (prefixWord ++ tailWord_4147596).sum := by decide
  have hdescent : baseEnd_4147596 < baseStart_4147596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147623 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_4147623 : Nat := 118140960795 + 4147623 * 2 ^ 59
def prefixEnd_4147623 : Nat := 4983230072969 + 3 ^ 40 * 4147623 * 2
def baseEnd_4147623 : Nat := 2129724172643131139637935

theorem tailTrace_4147623 : CollatzResearch.WordTrace tailWord_4147623 prefixEnd_4147623 2129724172643131139637935 := by
  unfold tailWord_4147623
  simp only [CollatzResearch.WordTrace]
  refine ⟨151276238652877703458279523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100850825768585135638853015 151276238652877703458279523)
  ·
    refine ⟨226914357979316555187419285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151276238652877703458279523 226914357979316555187419285)
    ·
      refine ⟨10636610530280463524410279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226914357979316555187419285 10636610530280463524410279)
      ·
        refine ⟨15954915795420695286615419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10636610530280463524410279 15954915795420695286615419)
        ·
          refine ⟨23932373693131042929923129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15954915795420695286615419 23932373693131042929923129)
          ·
            refine ⟨17949280269848282197442347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23932373693131042929923129 17949280269848282197442347)
            ·
              refine ⟨26923920404772423296163521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17949280269848282197442347 26923920404772423296163521)
              ·
                refine ⟨20192940303579317472122641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26923920404772423296163521 20192940303579317472122641)
                ·
                  refine ⟨15144705227684488104091981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20192940303579317472122641 15144705227684488104091981)
                  ·
                    refine ⟨5679264460381683039034493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15144705227684488104091981 5679264460381683039034493)
                    ·
                      refine ⟨2129724172643131139637935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5679264460381683039034493 2129724172643131139637935)
                      ·
                        rfl

theorem cell23_4147623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_4147623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147623 prefixEnd_4147623 := by exact prefixLift 4147623
  have htrace : WordTrace (prefixWord ++ tailWord_4147623) baseStart_4147623 baseEnd_4147623 := by
    simpa [prefixWord, tailWord_4147623, baseEnd_4147623] using wordTrace_append hprefix tailTrace_4147623
  have hstable : (prefixWord ++ tailWord_4147623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147623).length < 2 ^ (prefixWord ++ tailWord_4147623).sum := by decide
  have hdescent : baseEnd_4147623 < baseStart_4147623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147624 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4147624 : Nat := 118140960795 + 4147624 * 2 ^ 59
def prefixEnd_4147624 : Nat := 4983230072969 + 3 ^ 40 * 4147624 * 2
def baseEnd_4147624 : Nat := 2129724686123785635725431

theorem tailTrace_4147624 : CollatzResearch.WordTrace tailWord_4147624 prefixEnd_4147624 2129724686123785635725431 := by
  unfold tailWord_4147624
  simp only [CollatzResearch.WordTrace]
  refine ⟨75638137562937040314532963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100850850083916053752710617 75638137562937040314532963)
  ·
    refine ⟨113457206344405560471799445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75638137562937040314532963 113457206344405560471799445)
    ·
      refine ⟨5318306547394010647115599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113457206344405560471799445 5318306547394010647115599)
      ·
        refine ⟨7977459821091015970673399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5318306547394010647115599 7977459821091015970673399)
        ·
          refine ⟨11966189731636523956010099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7977459821091015970673399 11966189731636523956010099)
          ·
            refine ⟨17949284597454785934015149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966189731636523956010099 17949284597454785934015149)
            ·
              refine ⟨6730981724045544725255681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949284597454785934015149 6730981724045544725255681)
              ·
                refine ⟨5048236293034158543941761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6730981724045544725255681 5048236293034158543941761)
                ·
                  refine ⟨3786177219775618907956321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048236293034158543941761 3786177219775618907956321)
                  ·
                    refine ⟨2839632914831714180967241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3786177219775618907956321 2839632914831714180967241)
                    ·
                      refine ⟨2129724686123785635725431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839632914831714180967241 2129724686123785635725431)
                      ·
                        rfl

theorem cell23_4147624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4147624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147624 prefixEnd_4147624 := by exact prefixLift 4147624
  have htrace : WordTrace (prefixWord ++ tailWord_4147624) baseStart_4147624 baseEnd_4147624 := by
    simpa [prefixWord, tailWord_4147624, baseEnd_4147624] using wordTrace_append hprefix tailTrace_4147624
  have hstable : (prefixWord ++ tailWord_4147624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147624).length < 2 ^ (prefixWord ++ tailWord_4147624).sum := by decide
  have hdescent : baseEnd_4147624 < baseStart_4147624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147690 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_4147690 : Nat := 118140960795 + 4147690 * 2 ^ 59
def prefixEnd_4147690 : Nat := 4983230072969 + 3 ^ 40 * 4147690 * 2
def baseEnd_4147690 : Nat := 709919525282327459166709

theorem tailTrace_4147690 : CollatzResearch.WordTrace tailWord_4147690 prefixEnd_4147690 709919525282327459166709 := by
  unfold tailWord_4147690
  simp only [CollatzResearch.WordTrace]
  refine ⟨37819670585908743475242131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100852454895756649267312349 37819670585908743475242131)
  ·
    refine ⟨56729505878863115212863197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37819670585908743475242131 56729505878863115212863197)
    ·
      refine ⟨21273564704573668204823699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56729505878863115212863197 21273564704573668204823699)
      ·
        refine ⟨31910347056860502307235549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21273564704573668204823699 31910347056860502307235549)
        ·
          refine ⟨11966380146322688365213331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31910347056860502307235549 11966380146322688365213331)
          ·
            refine ⟨17949570219484032547819997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11966380146322688365213331 17949570219484032547819997)
            ·
              refine ⟨6731088832306512205432499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17949570219484032547819997 6731088832306512205432499)
              ·
                refine ⟨10096633248459768308148749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731088832306512205432499 10096633248459768308148749)
                ·
                  refine ⟨3786237468172413115555781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10096633248459768308148749 3786237468172413115555781)
                  ·
                    refine ⟨709919525282327459166709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786237468172413115555781 709919525282327459166709)
                    ·
                      rfl

theorem cell23_4147690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_4147690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147690 prefixEnd_4147690 := by exact prefixLift 4147690
  have htrace : WordTrace (prefixWord ++ tailWord_4147690) baseStart_4147690 baseEnd_4147690 := by
    simpa [prefixWord, tailWord_4147690, baseEnd_4147690] using wordTrace_append hprefix tailTrace_4147690
  have hstable : (prefixWord ++ tailWord_4147690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147690).length < 2 ^ (prefixWord ++ tailWord_4147690).sum := by decide
  have hdescent : baseEnd_4147690 < baseStart_4147690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147763 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 1, 6]
def baseStart_4147763 : Nat := 118140960795 + 4147763 * 2 ^ 59
def prefixEnd_4147763 : Nat := 4983230072969 + 3 ^ 40 * 4147763 * 2
def baseEnd_4147763 : Nat := 709932019978253530629097

theorem tailTrace_4147763 : CollatzResearch.WordTrace tailWord_4147763 prefixEnd_4147763 709932019978253530629097 := by
  unfold tailWord_4147763
  simp only [CollatzResearch.WordTrace]
  refine ⟨151281344872370507368375943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100854229914913671578917295 151281344872370507368375943)
  ·
    refine ⟨226922017308555761052563915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151281344872370507368375943 226922017308555761052563915)
    ·
      refine ⟨340383025962833641578845873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226922017308555761052563915 340383025962833641578845873)
      ·
        refine ⟨255287269472125231184134405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340383025962833641578845873 255287269472125231184134405)
        ·
          refine ⟨47866363026023480847025201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255287269472125231184134405 47866363026023480847025201)
          ·
            refine ⟨35899772269517610635268901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47866363026023480847025201 35899772269517610635268901)
            ·
              refine ⟨6731207300534551994112919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35899772269517610635268901 6731207300534551994112919)
              ·
                refine ⟨10096810950801827991169379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731207300534551994112919 10096810950801827991169379)
                ·
                  refine ⟨15145216426202741986754069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096810950801827991169379 15145216426202741986754069)
                  ·
                    refine ⟨709932019978253530629097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15145216426202741986754069 709932019978253530629097)
                    ·
                      rfl

theorem cell23_4147763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 6].length) (baseStart_4147763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147763 prefixEnd_4147763 := by exact prefixLift 4147763
  have htrace : WordTrace (prefixWord ++ tailWord_4147763) baseStart_4147763 baseEnd_4147763 := by
    simpa [prefixWord, tailWord_4147763, baseEnd_4147763] using wordTrace_append hprefix tailTrace_4147763
  have hstable : (prefixWord ++ tailWord_4147763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147763).length < 2 ^ (prefixWord ++ tailWord_4147763).sum := by decide
  have hdescent : baseEnd_4147763 < baseStart_4147763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147774 : List Nat := [4, 2, 1, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4147774 : Nat := 118140960795 + 4147774 * 2 ^ 59
def prefixEnd_4147774 : Nat := 4983230072969 + 3 ^ 40 * 4147774 * 2
def baseEnd_4147774 : Nat := 2129801708221960048849741

theorem tailTrace_4147774 : CollatzResearch.WordTrace tailWord_4147774 prefixEnd_4147774 2129801708221960048849741 := by
  unfold tailWord_4147774
  simp only [CollatzResearch.WordTrace]
  refine ⟨18910218259416332030878297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100854497383553770831350917 18910218259416332030878297)
  ·
    refine ⟨14182663694562249023158723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18910218259416332030878297 14182663694562249023158723)
    ·
      refine ⟨21273995541843373534738085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14182663694562249023158723 21273995541843373534738085)
      ·
        refine ⟨3988874164095632537763391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21273995541843373534738085 3988874164095632537763391)
        ·
          refine ⟨5983311246143448806645087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3988874164095632537763391 5983311246143448806645087)
          ·
            refine ⟨8974966869215173209967631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983311246143448806645087 8974966869215173209967631)
            ·
              refine ⟨13462450303822759814951447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8974966869215173209967631 13462450303822759814951447)
              ·
                refine ⟨20193675455734139722427171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13462450303822759814951447 20193675455734139722427171)
                ·
                  refine ⟨30290513183601209583640757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20193675455734139722427171 30290513183601209583640757)
                  ·
                    refine ⟨2839735610962613398466321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30290513183601209583640757 2839735610962613398466321)
                    ·
                      refine ⟨2129801708221960048849741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839735610962613398466321 2129801708221960048849741)
                      ·
                        rfl

theorem cell23_4147774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4147774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147774 prefixEnd_4147774 := by exact prefixLift 4147774
  have htrace : WordTrace (prefixWord ++ tailWord_4147774) baseStart_4147774 baseEnd_4147774 := by
    simpa [prefixWord, tailWord_4147774, baseEnd_4147774] using wordTrace_append hprefix tailTrace_4147774
  have hstable : (prefixWord ++ tailWord_4147774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147774).length < 2 ^ (prefixWord ++ tailWord_4147774).sum := by decide
  have hdescent : baseEnd_4147774 < baseStart_4147774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147776 : List Nat := [2, 1, 1, 2, 2, 2, 2, 11]
def baseStart_4147776 : Nat := 118140960795 + 4147776 * 2 ^ 59
def prefixEnd_4147776 : Nat := 4983230072969 + 3 ^ 40 * 4147776 * 2
def baseEnd_4147776 : Nat := 78881582784565520037953

theorem tailTrace_4147776 : CollatzResearch.WordTrace tailWord_4147776 prefixEnd_4147776 78881582784565520037953 := by
  unfold tailWord_4147776
  simp only [CollatzResearch.WordTrace]
  refine ⟨75640909510661705294299591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100854546014215607059066121 75640909510661705294299591)
  ·
    refine ⟨113461364265992557941449387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75640909510661705294299591 113461364265992557941449387)
    ·
      refine ⟨170192046398988836912174081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113461364265992557941449387 170192046398988836912174081)
      ·
        refine ⟨127644034799241627684130561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170192046398988836912174081 127644034799241627684130561)
        ·
          refine ⟨95733026099431220763097921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127644034799241627684130561 95733026099431220763097921)
          ·
            refine ⟨71799769574573415572323441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95733026099431220763097921 71799769574573415572323441)
            ·
              refine ⟨53849827180930061679242581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71799769574573415572323441 53849827180930061679242581)
              ·
                refine ⟨78881582784565520037953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53849827180930061679242581 78881582784565520037953)
                ·
                  rfl

theorem cell23_4147776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 11].length) (baseStart_4147776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147776 prefixEnd_4147776 := by exact prefixLift 4147776
  have htrace : WordTrace (prefixWord ++ tailWord_4147776) baseStart_4147776 baseEnd_4147776 := by
    simpa [prefixWord, tailWord_4147776, baseEnd_4147776] using wordTrace_append hprefix tailTrace_4147776
  have hstable : (prefixWord ++ tailWord_4147776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147776).length < 2 ^ (prefixWord ++ tailWord_4147776).sum := by decide
  have hdescent : baseEnd_4147776 < baseStart_4147776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147820 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 3]
def baseStart_4147820 : Nat := 118140960795 + 4147820 * 2 ^ 59
def prefixEnd_4147820 : Nat := 4983230072969 + 3 ^ 40 * 4147820 * 2
def baseEnd_4147820 : Nat := 2129825328332066868874529

theorem tailTrace_4147820 : CollatzResearch.WordTrace tailWord_4147820 prefixEnd_4147820 2129825328332066868874529 := by
  unfold tailWord_4147820
  simp only [CollatzResearch.WordTrace]
  refine ⟨75641711916582003051600457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100855615888776004068800609 75641711916582003051600457)
  ·
    refine ⟨56731283937436502288700343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75641711916582003051600457 56731283937436502288700343)
    ·
      refine ⟨85096925906154753433050515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56731283937436502288700343 85096925906154753433050515)
      ·
        refine ⟨127645388859232130149575773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85096925906154753433050515 127645388859232130149575773)
        ·
          refine ⟨47867020822212048806090915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127645388859232130149575773 47867020822212048806090915)
          ·
            refine ⟨71800531233318073209136373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47867020822212048806090915 71800531233318073209136373)
            ·
              refine ⟨6731299803123569363356535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71800531233318073209136373 6731299803123569363356535)
              ·
                refine ⟨10096949704685354045034803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731299803123569363356535 10096949704685354045034803)
                ·
                  refine ⟨15145424557028031067552205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10096949704685354045034803 15145424557028031067552205)
                  ·
                    refine ⟨5679534208885511650332077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15145424557028031067552205 5679534208885511650332077)
                    ·
                      refine ⟨2129825328332066868874529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5679534208885511650332077 2129825328332066868874529)
                      ·
                        rfl

theorem cell23_4147820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 3].length) (baseStart_4147820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147820 prefixEnd_4147820 := by exact prefixLift 4147820
  have htrace : WordTrace (prefixWord ++ tailWord_4147820) baseStart_4147820 baseEnd_4147820 := by
    simpa [prefixWord, tailWord_4147820, baseEnd_4147820] using wordTrace_append hprefix tailTrace_4147820
  have hstable : (prefixWord ++ tailWord_4147820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147820).length < 2 ^ (prefixWord ++ tailWord_4147820).sum := by decide
  have hdescent : baseEnd_4147820 < baseStart_4147820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147833 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_4147833 : Nat := 118140960795 + 4147833 * 2 ^ 59
def prefixEnd_4147833 : Nat := 4983230072969 + 3 ^ 40 * 4147833 * 2
def baseEnd_4147833 : Nat := 2129832003580575318011969

theorem tailTrace_4147833 : CollatzResearch.WordTrace tailWord_4147833 prefixEnd_4147833 2129832003580575318011969 := by
  unfold tailWord_4147833
  simp only [CollatzResearch.WordTrace]
  refine ⟨151283897982116909323424153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100855931988077939548949435 151283897982116909323424153)
  ·
    refine ⟨113462923486587681992568115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151283897982116909323424153 113462923486587681992568115)
    ·
      refine ⟨170194385229881522988852173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113462923486587681992568115 170194385229881522988852173)
      ·
        refine ⟨63822894461205571120819565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170194385229881522988852173 63822894461205571120819565)
        ·
          refine ⟨23933585422952089170307337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63822894461205571120819565 23933585422952089170307337)
          ·
            refine ⟨17950189067214066877730503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23933585422952089170307337 17950189067214066877730503)
            ·
              refine ⟨26925283600821100316595755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17950189067214066877730503 26925283600821100316595755)
              ·
                refine ⟨40387925401231650474893633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26925283600821100316595755 40387925401231650474893633)
                ·
                  refine ⟨30290944050923737856170225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40387925401231650474893633 30290944050923737856170225)
                  ·
                    refine ⟨22718208038192803392127669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30290944050923737856170225 22718208038192803392127669)
                    ·
                      refine ⟨2129832003580575318011969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22718208038192803392127669 2129832003580575318011969)
                      ·
                        rfl

theorem cell23_4147833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_4147833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147833 prefixEnd_4147833 := by exact prefixLift 4147833
  have htrace : WordTrace (prefixWord ++ tailWord_4147833) baseStart_4147833 baseEnd_4147833 := by
    simpa [prefixWord, tailWord_4147833, baseEnd_4147833] using wordTrace_append hprefix tailTrace_4147833
  have hstable : (prefixWord ++ tailWord_4147833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147833).length < 2 ^ (prefixWord ++ tailWord_4147833).sum := by decide
  have hdescent : baseEnd_4147833 < baseStart_4147833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147847 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_4147847 : Nat := 118140960795 + 4147847 * 2 ^ 59
def prefixEnd_4147847 : Nat := 4983230072969 + 3 ^ 40 * 4147847 * 2
def baseEnd_4147847 : Nat := 2129839192309738263236905

theorem tailTrace_4147847 : CollatzResearch.WordTrace tailWord_4147847 prefixEnd_4147847 2129839192309738263236905 := by
  unfold tailWord_4147847
  simp only [CollatzResearch.WordTrace]
  refine ⟨151284408604066189714433795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100856272402710793142955863 151284408604066189714433795)
  ·
    refine ⟨226926612906099284571650693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151284408604066189714433795 226926612906099284571650693)
    ·
      refine ⟨42548739919893615857184505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226926612906099284571650693 42548739919893615857184505)
      ·
        refine ⟨31911554939920211892888379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42548739919893615857184505 31911554939920211892888379)
        ·
          refine ⟨47867332409880317839332569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31911554939920211892888379 47867332409880317839332569)
          ·
            refine ⟨35900499307410238379499427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47867332409880317839332569 35900499307410238379499427)
            ·
              refine ⟨53850748961115357569249141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35900499307410238379499427 53850748961115357569249141)
              ·
                refine ⟨5048507715104564772117107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53850748961115357569249141 5048507715104564772117107)
                ·
                  refine ⟨7572761572656847158175661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048507715104564772117107 7572761572656847158175661)
                  ·
                    refine ⟨2839785589746317684315873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7572761572656847158175661 2839785589746317684315873)
                    ·
                      refine ⟨2129839192309738263236905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2839785589746317684315873 2129839192309738263236905)
                      ·
                        rfl

theorem cell23_4147847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_4147847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147847 prefixEnd_4147847 := by exact prefixLift 4147847
  have htrace : WordTrace (prefixWord ++ tailWord_4147847) baseStart_4147847 baseEnd_4147847 := by
    simpa [prefixWord, tailWord_4147847, baseEnd_4147847] using wordTrace_append hprefix tailTrace_4147847
  have hstable : (prefixWord ++ tailWord_4147847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147847).length < 2 ^ (prefixWord ++ tailWord_4147847).sum := by decide
  have hdescent : baseEnd_4147847 < baseStart_4147847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147863 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_4147863 : Nat := 118140960795 + 4147863 * 2 ^ 59
def prefixEnd_4147863 : Nat := 4983230072969 + 3 ^ 40 * 4147863 * 2
def baseEnd_4147863 : Nat := 2129847408000210200636831

theorem tailTrace_4147863 : CollatzResearch.WordTrace tailWord_4147863 prefixEnd_4147863 2129847408000210200636831 := by
  unfold tailWord_4147863
  simp only [CollatzResearch.WordTrace]
  refine ⟨151284992172008224447016243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100856661448005482964677495 151284992172008224447016243)
  ·
    refine ⟨226927488258012336670524365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151284992172008224447016243 226927488258012336670524365)
    ·
      refine ⟨85097808096754626251446637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226927488258012336670524365 85097808096754626251446637)
      ·
        refine ⟨31911678036282984844292489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85097808096754626251446637 31911678036282984844292489)
        ·
          refine ⟨23933758527212238633219367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31911678036282984844292489 23933758527212238633219367)
          ·
            refine ⟨35900637790818357949829051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23933758527212238633219367 35900637790818357949829051)
            ·
              refine ⟨53850956686227536924743577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35900637790818357949829051 53850956686227536924743577)
              ·
                refine ⟨40388217514670652693557683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53850956686227536924743577 40388217514670652693557683)
                ·
                  refine ⟨60582326272005979040336525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40388217514670652693557683 60582326272005979040336525)
                  ·
                    refine ⟨22718372352002242140126197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60582326272005979040336525 22718372352002242140126197)
                    ·
                      refine ⟨2129847408000210200636831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22718372352002242140126197 2129847408000210200636831)
                      ·
                        rfl

theorem cell23_4147863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_4147863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147863 prefixEnd_4147863 := by exact prefixLift 4147863
  have htrace : WordTrace (prefixWord ++ tailWord_4147863) baseStart_4147863 baseEnd_4147863 := by
    simpa [prefixWord, tailWord_4147863, baseEnd_4147863] using wordTrace_append hprefix tailTrace_4147863
  have hstable : (prefixWord ++ tailWord_4147863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147863).length < 2 ^ (prefixWord ++ tailWord_4147863).sum := by decide
  have hdescent : baseEnd_4147863 < baseStart_4147863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147870 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_4147870 : Nat := 118140960795 + 4147870 * 2 ^ 59
def prefixEnd_4147870 : Nat := 4983230072969 + 3 ^ 40 * 4147870 * 2
def baseEnd_4147870 : Nat := 709950334121597224416433

theorem tailTrace_4147870 : CollatzResearch.WordTrace tailWord_4147870 prefixEnd_4147870 709950334121597224416433 := by
  unfold tailWord_4147870
  simp only [CollatzResearch.WordTrace]
  refine ⟨18910655935372858080315133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100856831655321909761680709 18910655935372858080315133)
  ·
    refine ⟨7091495975764821780118175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18910655935372858080315133 7091495975764821780118175)
    ·
      refine ⟨10637243963647232670177263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7091495975764821780118175 10637243963647232670177263)
      ·
        refine ⟨15955865945470849005265895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10637243963647232670177263 15955865945470849005265895)
        ·
          refine ⟨23933798918206273507898843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15955865945470849005265895 23933798918206273507898843)
          ·
            refine ⟨35900698377309410261848265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23933798918206273507898843 35900698377309410261848265)
            ·
              refine ⟨26925523782982057696386199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35900698377309410261848265 26925523782982057696386199)
              ·
                refine ⟨40388285674473086544579299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26925523782982057696386199 40388285674473086544579299)
                ·
                  refine ⟨60582428511709629816868949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40388285674473086544579299 60582428511709629816868949)
                  ·
                    refine ⟨709950334121597224416433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60582428511709629816868949 709950334121597224416433)
                    ·
                      rfl

theorem cell23_4147870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_4147870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147870 prefixEnd_4147870 := by exact prefixLift 4147870
  have htrace : WordTrace (prefixWord ++ tailWord_4147870) baseStart_4147870 baseEnd_4147870 := by
    simpa [prefixWord, tailWord_4147870, baseEnd_4147870] using wordTrace_append hprefix tailTrace_4147870
  have hstable : (prefixWord ++ tailWord_4147870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147870).length < 2 ^ (prefixWord ++ tailWord_4147870).sum := by decide
  have hdescent : baseEnd_4147870 < baseStart_4147870 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4147960 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 5, 4]
def baseStart_4147960 : Nat := 118140960795 + 4147960 * 2 ^ 59
def prefixEnd_4147960 : Nat := 4983230072969 + 3 ^ 40 * 4147960 * 2
def baseEnd_4147960 : Nat := 709965738541232107041295

theorem tailTrace_4147960 : CollatzResearch.WordTrace tailWord_4147960 prefixEnd_4147960 709965738541232107041295 := by
  unfold tailWord_4147960
  simp only [CollatzResearch.WordTrace]
  refine ⟨75644265026328405006648667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100859020035104540008864889 75644265026328405006648667)
  ·
    refine ⟨113466397539492607509973001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75644265026328405006648667 113466397539492607509973001)
    ·
      refine ⟨85099798154619455632479751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113466397539492607509973001 85099798154619455632479751)
      ·
        refine ⟨127649697231929183448719627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85099798154619455632479751 127649697231929183448719627)
        ·
          refine ⟨191474545847893775173079441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127649697231929183448719627 191474545847893775173079441)
          ·
            refine ⟨143605909385920331379809581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191474545847893775173079441 143605909385920331379809581)
            ·
              refine ⟨53852216019720124267428593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143605909385920331379809581 53852216019720124267428593)
              ·
                refine ⟨40389162014790093200571445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53852216019720124267428593 40389162014790093200571445)
                ·
                  refine ⟨3786483938886571237553573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40389162014790093200571445 3786483938886571237553573)
                  ·
                    refine ⟨709965738541232107041295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786483938886571237553573 709965738541232107041295)
                    ·
                      rfl

theorem cell23_4147960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 4].length) (baseStart_4147960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4147960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4147960 prefixEnd_4147960 := by exact prefixLift 4147960
  have htrace : WordTrace (prefixWord ++ tailWord_4147960) baseStart_4147960 baseEnd_4147960 := by
    simpa [prefixWord, tailWord_4147960, baseEnd_4147960] using wordTrace_append hprefix tailTrace_4147960
  have hstable : (prefixWord ++ tailWord_4147960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4147960).length < 2 ^ (prefixWord ++ tailWord_4147960).sum := by decide
  have hdescent : baseEnd_4147960 < baseStart_4147960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4147960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148057 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_4148057 : Nat := 118140960795 + 4148057 * 2 ^ 59
def prefixEnd_4148057 : Nat := 4983230072969 + 3 ^ 40 * 4148057 * 2
def baseEnd_4148057 : Nat := 2129947023247182441610939

theorem tailTrace_4148057 : CollatzResearch.WordTrace tailWord_4148057 prefixEnd_4148057 2129947023247182441610939 := by
  unfold tailWord_4148057
  simp only [CollatzResearch.WordTrace]
  refine ⟨151292067933305395579578425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100861378622203597053052283 151292067933305395579578425)
  ·
    refine ⟨113469050949979046684683819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151292067933305395579578425 113469050949979046684683819)
    ·
      refine ⟨170203576424968570027025729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113469050949979046684683819 170203576424968570027025729)
      ·
        refine ⟨127652682318726427520269297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170203576424968570027025729 127652682318726427520269297)
        ·
          refine ⟨95739511739044820640201973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127652682318726427520269297 95739511739044820640201973)
          ·
            refine ⟨8975579225535451935018935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95739511739044820640201973 8975579225535451935018935)
            ·
              refine ⟨13463368838303177902528403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975579225535451935018935 13463368838303177902528403)
              ·
                refine ⟨20195053257454766853792605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13463368838303177902528403 20195053257454766853792605)
                ·
                  refine ⟨7573144971545537570172227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20195053257454766853792605 7573144971545537570172227)
                  ·
                    refine ⟨11359717457318306355258341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573144971545537570172227 11359717457318306355258341)
                    ·
                      refine ⟨2129947023247182441610939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11359717457318306355258341 2129947023247182441610939)
                      ·
                        rfl

theorem cell23_4148057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_4148057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148057 prefixEnd_4148057 := by exact prefixLift 4148057
  have htrace : WordTrace (prefixWord ++ tailWord_4148057) baseStart_4148057 baseEnd_4148057 := by
    simpa [prefixWord, tailWord_4148057, baseEnd_4148057] using wordTrace_append hprefix tailTrace_4148057
  have hstable : (prefixWord ++ tailWord_4148057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148057).length < 2 ^ (prefixWord ++ tailWord_4148057).sum := by decide
  have hdescent : baseEnd_4148057 < baseStart_4148057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148067 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 1, 6]
def baseStart_4148067 : Nat := 118140960795 + 4148067 * 2 ^ 59
def prefixEnd_4148067 : Nat := 4983230072969 + 3 ^ 40 * 4148067 * 2
def baseEnd_4148067 : Nat := 709984052684575800828631

theorem tailTrace_4148067 : CollatzResearch.WordTrace tailWord_4148067 prefixEnd_4148067 709984052684575800828631 := by
  unfold tailWord_4148067
  simp only [CollatzResearch.WordTrace]
  refine ⟨151292432663269167287442455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100861621775512778191628303 151292432663269167287442455)
  ·
    refine ⟨226938648994903750931163683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151292432663269167287442455 226938648994903750931163683)
    ·
      refine ⟨340407973492355626396745525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226938648994903750931163683 340407973492355626396745525)
      ·
        refine ⟨31913247514908339974694893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340407973492355626396745525 31913247514908339974694893)
        ·
          refine ⟨11967467818090627490510585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31913247514908339974694893 11967467818090627490510585)
          ·
            refine ⟨8975600863567970617882939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11967467818090627490510585 8975600863567970617882939)
            ·
              refine ⟨13463401295351955926824409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8975600863567970617882939 13463401295351955926824409)
              ·
                refine ⟨10097550971513966945118307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13463401295351955926824409 10097550971513966945118307)
                ·
                  refine ⟨15146326457270950417677461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097550971513966945118307 15146326457270950417677461)
                  ·
                    refine ⟨709984052684575800828631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15146326457270950417677461 709984052684575800828631)
                    ·
                      rfl

theorem cell23_4148067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 6].length) (baseStart_4148067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148067 prefixEnd_4148067 := by exact prefixLift 4148067
  have htrace : WordTrace (prefixWord ++ tailWord_4148067) baseStart_4148067 baseEnd_4148067 := by
    simpa [prefixWord, tailWord_4148067, baseEnd_4148067] using wordTrace_append hprefix tailTrace_4148067
  have hstable : (prefixWord ++ tailWord_4148067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148067).length < 2 ^ (prefixWord ++ tailWord_4148067).sum := by decide
  have hdescent : baseEnd_4148067 < baseStart_4148067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148085 : List Nat := [1, 3, 4, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_4148085 : Nat := 118140960795 + 4148085 * 2 ^ 59
def prefixEnd_4148085 : Nat := 4983230072969 + 3 ^ 40 * 4148085 * 2
def baseEnd_4148085 : Nat := 2129961400705508332060811

theorem tailTrace_4148085 : CollatzResearch.WordTrace tailWord_4148085 prefixEnd_4148085 2129961400705508332060811 := by
  unfold tailWord_4148085
  simp only [CollatzResearch.WordTrace]
  refine ⟨151293089177203956361597709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100862059451469304241065139 151293089177203956361597709)
  ·
    refine ⟨56734908441451483635599141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151293089177203956361597709 56734908441451483635599141)
    ·
      refine ⟨10637795332772153181674839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56734908441451483635599141 10637795332772153181674839)
      ·
        refine ⟨15956692999158229772512259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10637795332772153181674839 15956692999158229772512259)
        ·
          refine ⟨23935039498737344658768389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15956692999158229772512259 23935039498737344658768389)
          ·
            refine ⟨4487819906013252123519073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23935039498737344658768389 4487819906013252123519073)
            ·
              refine ⟨3365864929509939092639305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4487819906013252123519073 3365864929509939092639305)
              ·
                refine ⟨2524398697132454319479479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3365864929509939092639305 2524398697132454319479479)
                ·
                  refine ⟨3786598045698681479219219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524398697132454319479479 3786598045698681479219219)
                  ·
                    refine ⟨5679897068548022218828829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3786598045698681479219219 5679897068548022218828829)
                    ·
                      refine ⟨2129961400705508332060811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5679897068548022218828829 2129961400705508332060811)
                      ·
                        rfl

theorem cell23_4148085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_4148085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148085 prefixEnd_4148085 := by exact prefixLift 4148085
  have htrace : WordTrace (prefixWord ++ tailWord_4148085) baseStart_4148085 baseEnd_4148085 := by
    simpa [prefixWord, tailWord_4148085, baseEnd_4148085] using wordTrace_append hprefix tailTrace_4148085
  have hstable : (prefixWord ++ tailWord_4148085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148085).length < 2 ^ (prefixWord ++ tailWord_4148085).sum := by decide
  have hdescent : baseEnd_4148085 < baseStart_4148085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148104 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 1, 2, 4]
def baseStart_4148104 : Nat := 118140960795 + 4148104 * 2 ^ 59
def prefixEnd_4148104 : Nat := 4983230072969 + 3 ^ 40 * 4148104 * 2
def baseEnd_4148104 : Nat := 2129971156837943757723223

theorem tailTrace_4148104 : CollatzResearch.WordTrace tailWord_4148104 prefixEnd_4148104 2129971156837943757723223 := by
  unfold tailWord_4148104
  simp only [CollatzResearch.WordTrace]
  refine ⟨75646891082067561303269683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100862521442756748404359577 75646891082067561303269683)
  ·
    refine ⟨113470336623101341954904525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75646891082067561303269683 113470336623101341954904525)
    ·
      refine ⟨42551376233663003233089197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113470336623101341954904525 42551376233663003233089197)
      ·
        refine ⟨15956766087623626212408449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42551376233663003233089197 15956766087623626212408449)
        ·
          refine ⟨11967574565717719659306337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15956766087623626212408449 11967574565717719659306337)
          ·
            refine ⟨8975680924288289744479753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11967574565717719659306337 8975680924288289744479753)
            ·
              refine ⟨6731760693216217308359815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8975680924288289744479753 6731760693216217308359815)
              ·
                refine ⟨10097641039824325962539723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6731760693216217308359815 10097641039824325962539723)
                ·
                  refine ⟨15146461559736488943809585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097641039824325962539723 15146461559736488943809585)
                  ·
                    refine ⟨11359846169802366707857189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15146461559736488943809585 11359846169802366707857189)
                    ·
                      refine ⟨2129971156837943757723223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11359846169802366707857189 2129971156837943757723223)
                      ·
                        rfl

theorem cell23_4148104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_4148104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148104 prefixEnd_4148104 := by exact prefixLift 4148104
  have htrace : WordTrace (prefixWord ++ tailWord_4148104) baseStart_4148104 baseEnd_4148104 := by
    simpa [prefixWord, tailWord_4148104, baseEnd_4148104] using wordTrace_append hprefix tailTrace_4148104
  have hstable : (prefixWord ++ tailWord_4148104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148104).length < 2 ^ (prefixWord ++ tailWord_4148104).sum := by decide
  have hdescent : baseEnd_4148104 < baseStart_4148104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148107 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 3]
def baseStart_4148107 : Nat := 118140960795 + 4148107 * 2 ^ 59
def prefixEnd_4148107 : Nat := 4983230072969 + 3 ^ 40 * 4148107 * 2
def baseEnd_4148107 : Nat := 2129972697279907245985709

theorem tailTrace_4148107 : CollatzResearch.WordTrace tailWord_4148107 prefixEnd_4148107 2129972697279907245985709 := by
  unfold tailWord_4148107
  simp only [CollatzResearch.WordTrace]
  refine ⟨151293891583124254118898575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100862594388749502745932383 151293891583124254118898575)
  ·
    refine ⟨226940837374686381178347863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151293891583124254118898575 226940837374686381178347863)
    ·
      refine ⟨340411256062029571767521795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226940837374686381178347863 340411256062029571767521795)
      ·
        refine ⟨510616884093044357651282693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340411256062029571767521795 510616884093044357651282693)
        ·
          refine ⟨95740665767445817059615505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510616884093044357651282693 95740665767445817059615505)
          ·
            refine ⟨71805499325584362794711629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95740665767445817059615505 71805499325584362794711629)
            ·
              refine ⟨26927062247094136048016861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71805499325584362794711629 26927062247094136048016861)
              ·
                refine ⟨10097648342660301018006323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26927062247094136048016861 10097648342660301018006323)
                ·
                  refine ⟨15146472513990451527009485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10097648342660301018006323 15146472513990451527009485)
                  ·
                    refine ⟨5679927192746419322628557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15146472513990451527009485 5679927192746419322628557)
                    ·
                      refine ⟨2129972697279907245985709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5679927192746419322628557 2129972697279907245985709)
                      ·
                        rfl

theorem cell23_4148107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 3].length) (baseStart_4148107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148107 prefixEnd_4148107 := by exact prefixLift 4148107
  have htrace : WordTrace (prefixWord ++ tailWord_4148107) baseStart_4148107 baseEnd_4148107 := by
    simpa [prefixWord, tailWord_4148107, baseEnd_4148107] using wordTrace_append hprefix tailTrace_4148107
  have hstable : (prefixWord ++ tailWord_4148107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148107).length < 2 ^ (prefixWord ++ tailWord_4148107).sum := by decide
  have hdescent : baseEnd_4148107 < baseStart_4148107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148140 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_4148140 : Nat := 118140960795 + 4148140 * 2 ^ 59
def prefixEnd_4148140 : Nat := 4983230072969 + 3 ^ 40 * 4148140 * 2
def baseEnd_4148140 : Nat := 709996547380501872291019

theorem tailTrace_4148140 : CollatzResearch.WordTrace tailWord_4148140 prefixEnd_4148140 709996547380501872291019 := by
  unfold tailWord_4148140
  simp only [CollatzResearch.WordTrace]
  refine ⟨75647547596002350377424937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100863396794669800503233249 75647547596002350377424937)
  ·
    refine ⟨56735660697001762783068703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75647547596002350377424937 56735660697001762783068703)
    ·
      refine ⟨85103491045502644174603055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56735660697001762783068703 85103491045502644174603055)
      ·
        refine ⟨127655236568253966261904583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85103491045502644174603055 127655236568253966261904583)
        ·
          refine ⟨191482854852380949392856875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127655236568253966261904583 191482854852380949392856875)
          ·
            refine ⟨287224282278571424089285313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191482854852380949392856875 287224282278571424089285313)
            ·
              refine ⟨215418211708928568066963985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287224282278571424089285313 215418211708928568066963985)
              ·
                refine ⟨161563658781696426050222989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215418211708928568066963985 161563658781696426050222989)
                ·
                  refine ⟨60586372043136159768833621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161563658781696426050222989 60586372043136159768833621)
                  ·
                    refine ⟨709996547380501872291019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60586372043136159768833621 709996547380501872291019)
                    ·
                      rfl

theorem cell23_4148140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_4148140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148140 prefixEnd_4148140 := by exact prefixLift 4148140
  have htrace : WordTrace (prefixWord ++ tailWord_4148140) baseStart_4148140 baseEnd_4148140 := by
    simpa [prefixWord, tailWord_4148140, baseEnd_4148140] using wordTrace_append hprefix tailTrace_4148140
  have hstable : (prefixWord ++ tailWord_4148140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148140).length < 2 ^ (prefixWord ++ tailWord_4148140).sum := by decide
  have hdescent : baseEnd_4148140 < baseStart_4148140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148158 : List Nat := [4, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_4148158 : Nat := 118140960795 + 4148158 * 2 ^ 59
def prefixEnd_4148158 : Nat := 4983230072969 + 3 ^ 40 * 4148158 * 2
def baseEnd_4148158 : Nat := 2129998884793286546447975

theorem tailTrace_4148158 : CollatzResearch.WordTrace tailWord_4148158 prefixEnd_4148158 2129998884793286546447975 := by
  unfold tailWord_4148158
  simp only [CollatzResearch.WordTrace]
  refine ⟨18911968963242436228625641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100863834470626326552670085 18911968963242436228625641)
  ·
    refine ⟨14183976722431827171469231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18911968963242436228625641 14183976722431827171469231)
    ·
      refine ⟨21275965083647740757203847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14183976722431827171469231 21275965083647740757203847)
      ·
        refine ⟨31913947625471611135805771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21275965083647740757203847 31913947625471611135805771)
        ·
          refine ⟨47870921438207416703708657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31913947625471611135805771 47870921438207416703708657)
          ·
            refine ⟨35903191078655562527781493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47870921438207416703708657 35903191078655562527781493)
            ·
              refine ⟨3365924163623958986979515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35903191078655562527781493 3365924163623958986979515)
              ·
                refine ⟨5048886245435938480469273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3365924163623958986979515 5048886245435938480469273)
                ·
                  refine ⟨3786664684076953860351955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5048886245435938480469273 3786664684076953860351955)
                  ·
                    refine ⟨5679997026115430790527933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3786664684076953860351955 5679997026115430790527933)
                    ·
                      refine ⟨2129998884793286546447975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5679997026115430790527933 2129998884793286546447975)
                      ·
                        rfl

theorem cell23_4148158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_4148158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148158 prefixEnd_4148158 := by exact prefixLift 4148158
  have htrace : WordTrace (prefixWord ++ tailWord_4148158) baseStart_4148158 baseEnd_4148158 := by
    simpa [prefixWord, tailWord_4148158, baseEnd_4148158] using wordTrace_append hprefix tailTrace_4148158
  have hstable : (prefixWord ++ tailWord_4148158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148158).length < 2 ^ (prefixWord ++ tailWord_4148158).sum := by decide
  have hdescent : baseEnd_4148158 < baseStart_4148158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148167 : List Nat := [1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_4148167 : Nat := 118140960795 + 4148167 * 2 ^ 59
def prefixEnd_4148167 : Nat := 4983230072969 + 3 ^ 40 * 4148167 * 2
def baseEnd_4148167 : Nat := 2130003506119177011235433

theorem tailTrace_4148167 : CollatzResearch.WordTrace tailWord_4148167 prefixEnd_4148167 2130003506119177011235433 := by
  unfold tailWord_4148167
  simp only [CollatzResearch.WordTrace]
  refine ⟨151296079962906884366082755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100864053308604589577388503 151296079962906884366082755)
  ·
    refine ⟨226944119944360326549124133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151296079962906884366082755 226944119944360326549124133)
    ·
      refine ⟨42552022489567561227960775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226944119944360326549124133 42552022489567561227960775)
      ·
        refine ⟨63828033734351341841941163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42552022489567561227960775 63828033734351341841941163)
        ·
          refine ⟨95742050601527012762911745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63828033734351341841941163 95742050601527012762911745)
          ·
            refine ⟨71806537951145259572183809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95742050601527012762911745 71806537951145259572183809)
            ·
              refine ⟨53854903463358944679137857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71806537951145259572183809 53854903463358944679137857)
              ·
                refine ⟨40391177597519208509353393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53854903463358944679137857 40391177597519208509353393)
                ·
                  refine ⟨30293383198139406382015045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40391177597519208509353393 30293383198139406382015045)
                  ·
                    refine ⟨5680009349651138696627821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30293383198139406382015045 5680009349651138696627821)
                    ·
                      refine ⟨2130003506119177011235433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5680009349651138696627821 2130003506119177011235433)
                      ·
                        rfl

theorem cell23_4148167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_4148167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148167 prefixEnd_4148167 := by exact prefixLift 4148167
  have htrace : WordTrace (prefixWord ++ tailWord_4148167) baseStart_4148167 baseEnd_4148167 := by
    simpa [prefixWord, tailWord_4148167, baseEnd_4148167] using wordTrace_append hprefix tailTrace_4148167
  have hstable : (prefixWord ++ tailWord_4148167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148167).length < 2 ^ (prefixWord ++ tailWord_4148167).sum := by decide
  have hdescent : baseEnd_4148167 < baseStart_4148167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148168 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 1, 3, 2]
def baseStart_4148168 : Nat := 118140960795 + 4148168 * 2 ^ 59
def prefixEnd_4148168 : Nat := 4983230072969 + 3 ^ 40 * 4148168 * 2
def baseEnd_4148168 : Nat := 2130004019599831507322929

theorem tailTrace_4148168 : CollatzResearch.WordTrace tailWord_4148168 prefixEnd_4148168 2130004019599831507322929 := by
  unfold tailWord_4148168
  simp only [CollatzResearch.WordTrace]
  refine ⟨75648058217951630768434579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100864077623935507691246105 75648058217951630768434579)
  ·
    refine ⟨113472087326927446152651869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75648058217951630768434579 113472087326927446152651869)
    ·
      refine ⟨42552032747597792307244451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113472087326927446152651869 42552032747597792307244451)
      ·
        refine ⟨63828049121396688460866677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42552032747597792307244451 63828049121396688460866677)
        ·
          refine ⟨5983879605130939543206251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63828049121396688460866677 5983879605130939543206251)
          ·
            refine ⟨8975819407696409314809377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5983879605130939543206251 8975819407696409314809377)
            ·
              refine ⟨6731864555772306986107033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8975819407696409314809377 6731864555772306986107033)
              ·
                refine ⟨5048898416829230239580275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6731864555772306986107033 5048898416829230239580275)
                ·
                  refine ⟨7573347625243845359370413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5048898416829230239580275 7573347625243845359370413)
                  ·
                    refine ⟨2840005359466442009763905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7573347625243845359370413 2840005359466442009763905)
                    ·
                      refine ⟨2130004019599831507322929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2840005359466442009763905 2130004019599831507322929)
                      ·
                        rfl

theorem cell23_4148168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 1, 3, 2].length) (baseStart_4148168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148168 prefixEnd_4148168 := by exact prefixLift 4148168
  have htrace : WordTrace (prefixWord ++ tailWord_4148168) baseStart_4148168 baseEnd_4148168 := by
    simpa [prefixWord, tailWord_4148168, baseEnd_4148168] using wordTrace_append hprefix tailTrace_4148168
  have hstable : (prefixWord ++ tailWord_4148168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148168).length < 2 ^ (prefixWord ++ tailWord_4148168).sum := by decide
  have hdescent : baseEnd_4148168 < baseStart_4148168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148217 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_4148217 : Nat := 118140960795 + 4148217 * 2 ^ 59
def prefixEnd_4148217 : Nat := 4983230072969 + 3 ^ 40 * 4148217 * 2
def baseEnd_4148217 : Nat := 710009726717300605203401

theorem tailTrace_4148217 : CollatzResearch.WordTrace tailWord_4148217 prefixEnd_4148217 710009726717300605203401 := by
  unfold tailWord_4148217
  simp only [CollatzResearch.WordTrace]
  refine ⟨151297903612725742905402905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100865269075150495270268603 151297903612725742905402905)
  ·
    refine ⟨113473427709544307179052179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151297903612725742905402905 113473427709544307179052179)
    ·
      refine ⟨170210141564316460768578269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113473427709544307179052179 170210141564316460768578269)
      ·
        refine ⟨63828803086618672788216851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170210141564316460768578269 63828803086618672788216851)
        ·
          refine ⟨95743204629928009182325277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63828803086618672788216851 95743204629928009182325277)
          ·
            refine ⟨35903701736223003443371979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95743204629928009182325277 35903701736223003443371979)
            ·
              refine ⟨53855552604334505165057969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35903701736223003443371979 53855552604334505165057969)
              ·
                refine ⟨40391664453250878873793477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53855552604334505165057969 40391664453250878873793477)
                ·
                  refine ⟨7573437084984539788836277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40391664453250878873793477 7573437084984539788836277)
                  ·
                    refine ⟨710009726717300605203401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7573437084984539788836277 710009726717300605203401)
                    ·
                      rfl

theorem cell23_4148217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_4148217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148217 prefixEnd_4148217 := by exact prefixLift 4148217
  have htrace : WordTrace (prefixWord ++ tailWord_4148217) baseStart_4148217 baseEnd_4148217 := by
    simpa [prefixWord, tailWord_4148217, baseEnd_4148217] using wordTrace_append hprefix tailTrace_4148217
  have hstable : (prefixWord ++ tailWord_4148217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148217).length < 2 ^ (prefixWord ++ tailWord_4148217).sum := by decide
  have hdescent : baseEnd_4148217 < baseStart_4148217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148234 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_4148234 : Nat := 118140960795 + 4148234 * 2 ^ 59
def prefixEnd_4148234 : Nat := 4983230072969 + 3 ^ 40 * 4148234 * 2
def baseEnd_4148234 : Nat := 710012636441009416365875

theorem tailTrace_4148234 : CollatzResearch.WordTrace tailWord_4148234 prefixEnd_4148234 710012636441009416365875 := by
  unfold tailWord_4148234
  simp only [CollatzResearch.WordTrace]
  refine ⟨37824630913416038702192939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100865682435776103205847837 37824630913416038702192939)
  ·
    refine ⟨56736946370124058053289409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37824630913416038702192939 56736946370124058053289409)
    ·
      refine ⟨42552709777593043539967057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56736946370124058053289409 42552709777593043539967057)
      ·
        refine ⟨31914532333194782654975293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42552709777593043539967057 31914532333194782654975293)
        ·
          refine ⟨11967949624948043495615735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31914532333194782654975293 11967949624948043495615735)
          ·
            refine ⟨17951924437422065243423603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11967949624948043495615735 17951924437422065243423603)
            ·
              refine ⟨26927886656133097865135405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17951924437422065243423603 26927886656133097865135405)
              ·
                refine ⟨10097957496049911699425777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26927886656133097865135405 10097957496049911699425777)
                ·
                  refine ⟨7573468122037433774569333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10097957496049911699425777 7573468122037433774569333)
                  ·
                    refine ⟨710012636441009416365875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7573468122037433774569333 710012636441009416365875)
                    ·
                      rfl

theorem cell23_4148234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_4148234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148234 prefixEnd_4148234 := by exact prefixLift 4148234
  have htrace : WordTrace (prefixWord ++ tailWord_4148234) baseStart_4148234 baseEnd_4148234 := by
    simpa [prefixWord, tailWord_4148234, baseEnd_4148234] using wordTrace_append hprefix tailTrace_4148234
  have hstable : (prefixWord ++ tailWord_4148234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148234).length < 2 ^ (prefixWord ++ tailWord_4148234).sum := by decide
  have hdescent : baseEnd_4148234 < baseStart_4148234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148274 : List Nat := [3, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_4148274 : Nat := 118140960795 + 4148274 * 2 ^ 59
def prefixEnd_4148274 : Nat := 4983230072969 + 3 ^ 40 * 4148274 * 2
def baseEnd_4148274 : Nat := 2130058448549208092597441

theorem tailTrace_4148274 : CollatzResearch.WordTrace tailWord_4148274 prefixEnd_4148274 2130058448549208092597441 := by
  unfold tailWord_4148274
  simp only [CollatzResearch.WordTrace]
  refine ⟨37824995643379810410056969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100866655049012827760151917 37824995643379810410056969)
  ·
    refine ⟨28368746732534857807542727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37824995643379810410056969 28368746732534857807542727)
    ·
      refine ⟨42553120098802286711314091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28368746732534857807542727 42553120098802286711314091)
      ·
        refine ⟨63829680148203430066971137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42553120098802286711314091 63829680148203430066971137)
        ·
          refine ⟨47872260111152572550228353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63829680148203430066971137 47872260111152572550228353)
          ·
            refine ⟨35904195083364429412671265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47872260111152572550228353 35904195083364429412671265)
            ·
              refine ⟨26928146312523322059503449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35904195083364429412671265 26928146312523322059503449)
              ·
                refine ⟨20196109734392491544627587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26928146312523322059503449 20196109734392491544627587)
                ·
                  refine ⟨30294164601588737316941381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20196109734392491544627587 30294164601588737316941381)
                  ·
                    refine ⟨5680155862797888246926509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30294164601588737316941381 5680155862797888246926509)
                    ·
                      refine ⟨2130058448549208092597441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5680155862797888246926509 2130058448549208092597441)
                      ·
                        rfl

theorem cell23_4148274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_4148274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148274 prefixEnd_4148274 := by exact prefixLift 4148274
  have htrace : WordTrace (prefixWord ++ tailWord_4148274) baseStart_4148274 baseEnd_4148274 := by
    simpa [prefixWord, tailWord_4148274, baseEnd_4148274] using wordTrace_append hprefix tailTrace_4148274
  have hstable : (prefixWord ++ tailWord_4148274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148274).length < 2 ^ (prefixWord ++ tailWord_4148274).sum := by decide
  have hdescent : baseEnd_4148274 < baseStart_4148274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148277 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 10]
def baseStart_4148277 : Nat := 118140960795 + 4148277 * 2 ^ 59
def prefixEnd_4148277 : Nat := 4983230072969 + 3 ^ 40 * 4148277 * 2
def baseEnd_4148277 : Nat := 236673332110130175651103

theorem tailTrace_4148277 : CollatzResearch.WordTrace tailWord_4148277 prefixEnd_4148277 236673332110130175651103 := by
  unfold tailWord_4148277
  simp only [CollatzResearch.WordTrace]
  refine ⟨151300091992508373152587085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100866727995005582101724723 151300091992508373152587085)
  ·
    refine ⟨56737534497190639932220157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151300091992508373152587085 56737534497190639932220157)
    ·
      refine ⟨21276575436446489974582559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56737534497190639932220157 21276575436446489974582559)
      ·
        refine ⟨31914863154669734961873839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21276575436446489974582559 31914863154669734961873839)
        ·
          refine ⟨47872294732004602442810759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31914863154669734961873839 47872294732004602442810759)
          ·
            refine ⟨71808442098006903664216139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47872294732004602442810759 71808442098006903664216139)
            ·
              refine ⟨107712663147010355496324209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71808442098006903664216139 107712663147010355496324209)
              ·
                refine ⟨80784497360257766622243157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107712663147010355496324209 80784497360257766622243157)
                ·
                  refine ⟨236673332110130175651103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 80784497360257766622243157 236673332110130175651103)
                  ·
                    rfl

theorem cell23_4148277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_4148277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148277 prefixEnd_4148277 := by exact prefixLift 4148277
  have htrace : WordTrace (prefixWord ++ tailWord_4148277) baseStart_4148277 baseEnd_4148277 := by
    simpa [prefixWord, tailWord_4148277, baseEnd_4148277] using wordTrace_append hprefix tailTrace_4148277
  have hstable : (prefixWord ++ tailWord_4148277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148277).length < 2 ^ (prefixWord ++ tailWord_4148277).sum := by decide
  have hdescent : baseEnd_4148277 < baseStart_4148277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148281 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 3, 4]
def baseStart_4148281 : Nat := 118140960795 + 4148281 * 2 ^ 59
def prefixEnd_4148281 : Nat := 4983230072969 + 3 ^ 40 * 4148281 * 2
def baseEnd_4148281 : Nat := 710020680971263188403303

theorem tailTrace_4148281 : CollatzResearch.WordTrace tailWord_4148281 prefixEnd_4148281 710020680971263188403303 := by
  unfold tailWord_4148281
  simp only [CollatzResearch.WordTrace]
  refine ⟨151300237884493881835732697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100866825256329254557155131 151300237884493881835732697)
  ·
    refine ⟨113475178413370411376799523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151300237884493881835732697 113475178413370411376799523)
    ·
      refine ⟨170212767620055617065199285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113475178413370411376799523 170212767620055617065199285)
      ·
        refine ⟨15957446964380214099862433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170212767620055617065199285 15957446964380214099862433)
        ·
          refine ⟨11968085223285160574896825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15957446964380214099862433 11968085223285160574896825)
          ·
            refine ⟨8976063917463870431172619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11968085223285160574896825 8976063917463870431172619)
            ·
              refine ⟨13464095876195805646758929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976063917463870431172619 13464095876195805646758929)
              ·
                refine ⟨10098071907146854235069197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13464095876195805646758929 10098071907146854235069197)
                ·
                  refine ⟨3786776965180070338150949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10098071907146854235069197 3786776965180070338150949)
                  ·
                    refine ⟨710020680971263188403303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786776965180070338150949 710020680971263188403303)
                    ·
                      rfl

theorem cell23_4148281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 4].length) (baseStart_4148281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148281 prefixEnd_4148281 := by exact prefixLift 4148281
  have htrace : WordTrace (prefixWord ++ tailWord_4148281) baseStart_4148281 baseEnd_4148281 := by
    simpa [prefixWord, tailWord_4148281, baseEnd_4148281] using wordTrace_append hprefix tailTrace_4148281
  have hstable : (prefixWord ++ tailWord_4148281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148281).length < 2 ^ (prefixWord ++ tailWord_4148281).sum := by decide
  have hdescent : baseEnd_4148281 < baseStart_4148281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148321 : List Nat := [1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_4148321 : Nat := 118140960795 + 4148321 * 2 ^ 59
def prefixEnd_4148321 : Nat := 4983230072969 + 3 ^ 40 * 4148321 * 2
def baseEnd_4148321 : Nat := 2130082582139969408709725

theorem tailTrace_4148321 : CollatzResearch.WordTrace tailWord_4148321 prefixEnd_4148321 2130082582139969408709725 := by
  unfold tailWord_4148321
  simp only [CollatzResearch.WordTrace]
  refine ⟨151301696804348968667188817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100867797869565979111459211 151301696804348968667188817)
  ·
    refine ⟨113476272603261726500391613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151301696804348968667188817 113476272603261726500391613)
    ·
      refine ⟨42553602226223147437646855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113476272603261726500391613 42553602226223147437646855)
      ·
        refine ⟨63830403339334721156470283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42553602226223147437646855 63830403339334721156470283)
        ·
          refine ⟨95745605009002081734705425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63830403339334721156470283 95745605009002081734705425)
          ·
            refine ⟨71809203756751561301029069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95745605009002081734705425 71809203756751561301029069)
            ·
              refine ⟨26928451408781835487885901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71809203756751561301029069 26928451408781835487885901)
              ·
                refine ⟨10098169278293188307957213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26928451408781835487885901 10098169278293188307957213)
                ·
                  refine ⟨3786813479359945615483955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10098169278293188307957213 3786813479359945615483955)
                  ·
                    refine ⟨5680220219039918423225933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3786813479359945615483955 5680220219039918423225933)
                    ·
                      refine ⟨2130082582139969408709725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5680220219039918423225933 2130082582139969408709725)
                      ·
                        rfl

theorem cell23_4148321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_4148321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148321 prefixEnd_4148321 := by exact prefixLift 4148321
  have htrace : WordTrace (prefixWord ++ tailWord_4148321) baseStart_4148321 baseEnd_4148321 := by
    simpa [prefixWord, tailWord_4148321, baseEnd_4148321] using wordTrace_append hprefix tailTrace_4148321
  have hstable : (prefixWord ++ tailWord_4148321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148321).length < 2 ^ (prefixWord ++ tailWord_4148321).sum := by decide
  have hdescent : baseEnd_4148321 < baseStart_4148321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148344 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_4148344 : Nat := 118140960795 + 4148344 * 2 ^ 59
def prefixEnd_4148344 : Nat := 4983230072969 + 3 ^ 40 * 4148344 * 2
def baseEnd_4148344 : Nat := 2130094392195022818722119

theorem tailTrace_4148344 : CollatzResearch.WordTrace tailWord_4148344 prefixEnd_4148344 2130094392195022818722119 := by
  unfold tailWord_4148344
  simp only [CollatzResearch.WordTrace]
  refine ⟨75651267841632821797638043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100868357122177095730184057 75651267841632821797638043)
  ·
    refine ⟨113476901762449232696457065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75651267841632821797638043 113476901762449232696457065)
    ·
      refine ⟨85107676321836924522342799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113476901762449232696457065 85107676321836924522342799)
      ·
        refine ⟨127661514482755386783514199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85107676321836924522342799 127661514482755386783514199)
        ·
          refine ⟨191492271724133080175271299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127661514482755386783514199 191492271724133080175271299)
          ·
            refine ⟨287238407586199620262906949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191492271724133080175271299 287238407586199620262906949)
            ·
              refine ⟨53857201422412428799295053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287238407586199620262906949 53857201422412428799295053)
              ·
                refine ⟨20196450533404660799735645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53857201422412428799295053 20196450533404660799735645)
                ·
                  refine ⟨7573668950026747799900867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20196450533404660799735645 7573668950026747799900867)
                  ·
                    refine ⟨11360503425040121699851301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573668950026747799900867 11360503425040121699851301)
                    ·
                      refine ⟨2130094392195022818722119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11360503425040121699851301 2130094392195022818722119)
                      ·
                        rfl

theorem cell23_4148344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_4148344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148344 prefixEnd_4148344 := by exact prefixLift 4148344
  have htrace : WordTrace (prefixWord ++ tailWord_4148344) baseStart_4148344 baseEnd_4148344 := by
    simpa [prefixWord, tailWord_4148344, baseEnd_4148344] using wordTrace_append hprefix tailTrace_4148344
  have hstable : (prefixWord ++ tailWord_4148344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148344).length < 2 ^ (prefixWord ++ tailWord_4148344).sum := by decide
  have hdescent : baseEnd_4148344 < baseStart_4148344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148361 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 4]
def baseStart_4148361 : Nat := 118140960795 + 4148361 * 2 ^ 59
def prefixEnd_4148361 : Nat := 4983230072969 + 3 ^ 40 * 4148361 * 2
def baseEnd_4148361 : Nat := 2130103121366149252209541

theorem tailTrace_4148361 : CollatzResearch.WordTrace tailWord_4148361 prefixEnd_4148361 2130103121366149252209541 := by
  unfold tailWord_4148361
  simp only [CollatzResearch.WordTrace]
  refine ⟨151303155724204055498644937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100868770482802703665763291 151303155724204055498644937)
  ·
    refine ⟨113477366793153041623983703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151303155724204055498644937 113477366793153041623983703)
    ·
      refine ⟨170216050189729562435975555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113477366793153041623983703 170216050189729562435975555)
      ·
        refine ⟨255324075284594343653963333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170216050189729562435975555 255324075284594343653963333)
        ·
          refine ⟨47873264115861439435118125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255324075284594343653963333 47873264115861439435118125)
          ·
            refine ⟨17952474043448039788169297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47873264115861439435118125 17952474043448039788169297)
            ·
              refine ⟨13464355532586029841126973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17952474043448039788169297 13464355532586029841126973)
              ·
                refine ⟨5049133324719761190422615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13464355532586029841126973 5049133324719761190422615)
                ·
                  refine ⟨7573699987079641785633923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5049133324719761190422615 7573699987079641785633923)
                  ·
                    refine ⟨11360549980619462678450885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7573699987079641785633923 11360549980619462678450885)
                    ·
                      refine ⟨2130103121366149252209541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11360549980619462678450885 2130103121366149252209541)
                      ·
                        rfl

theorem cell23_4148361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_4148361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148361 prefixEnd_4148361 := by exact prefixLift 4148361
  have htrace : WordTrace (prefixWord ++ tailWord_4148361) baseStart_4148361 baseEnd_4148361 := by
    simpa [prefixWord, tailWord_4148361, baseEnd_4148361] using wordTrace_append hprefix tailTrace_4148361
  have hstable : (prefixWord ++ tailWord_4148361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148361).length < 2 ^ (prefixWord ++ tailWord_4148361).sum := by decide
  have hdescent : baseEnd_4148361 < baseStart_4148361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148381 : List Nat := [1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_4148381 : Nat := 118140960795 + 4148381 * 2 ^ 59
def prefixEnd_4148381 : Nat := 4983230072969 + 3 ^ 40 * 4148381 * 2
def baseEnd_4148381 : Nat := 2130113390979239173959449

theorem tailTrace_4148381 : CollatzResearch.WordTrace tailWord_4148381 prefixEnd_4148381 2130113390979239173959449 := by
  unfold tailWord_4148381
  simp only [CollatzResearch.WordTrace]
  refine ⟨151303885184131598914372997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100869256789421065942915331 151303885184131598914372997)
  ·
    refine ⟨28369478472024674796444937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151303885184131598914372997 28369478472024674796444937)
    ·
      refine ⟨21277108854018506097333703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28369478472024674796444937 21277108854018506097333703)
      ·
        refine ⟨31915663281027759146000555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21277108854018506097333703 31915663281027759146000555)
        ·
          refine ⟨47873494921541638719000833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31915663281027759146000555 47873494921541638719000833)
          ·
            refine ⟨35905121191156229039250625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47873494921541638719000833 35905121191156229039250625)
            ·
              refine ⟨26928840893367171779437969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35905121191156229039250625 26928840893367171779437969)
              ·
                refine ⟨20196630670025378834578477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26928840893367171779437969 20196630670025378834578477)
                ·
                  refine ⟨7573736501259517062966929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20196630670025378834578477 7573736501259517062966929)
                  ·
                    refine ⟨5680302375944637797225197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7573736501259517062966929 5680302375944637797225197)
                    ·
                      refine ⟨2130113390979239173959449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5680302375944637797225197 2130113390979239173959449)
                      ·
                        rfl

theorem cell23_4148381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_4148381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148381 prefixEnd_4148381 := by exact prefixLift 4148381
  have htrace : WordTrace (prefixWord ++ tailWord_4148381) baseStart_4148381 baseEnd_4148381 := by
    simpa [prefixWord, tailWord_4148381, baseEnd_4148381] using wordTrace_append hprefix tailTrace_4148381
  have hstable : (prefixWord ++ tailWord_4148381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148381).length < 2 ^ (prefixWord ++ tailWord_4148381).sum := by decide
  have hdescent : baseEnd_4148381 < baseStart_4148381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148384 : List Nat := [2, 1, 1, 4, 2, 1, 4, 8]
def baseStart_4148384 : Nat := 118140960795 + 4148384 * 2 ^ 59
def prefixEnd_4148384 : Nat := 4983230072969 + 3 ^ 40 * 4148384 * 2
def baseEnd_4148384 : Nat := 78893145608192691193405

theorem tailTrace_4148384 : CollatzResearch.WordTrace tailWord_4148384 prefixEnd_4148384 78893145608192691193405 := by
  unfold tailWord_4148384
  simp only [CollatzResearch.WordTrace]
  refine ⟨75651997301560365213366103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100869329735413820284488137 75651997301560365213366103)
  ·
    refine ⟨113477995952340547820049155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75651997301560365213366103 113477995952340547820049155)
    ·
      refine ⟨170216993928510821730073733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113477995952340547820049155 170216993928510821730073733)
      ·
        refine ⟨31915686361595779074388825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170216993928510821730073733 31915686361595779074388825)
        ·
          refine ⟨23936764771196834305791619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31915686361595779074388825 23936764771196834305791619)
          ·
            refine ⟨35905147156795251458687429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23936764771196834305791619 35905147156795251458687429)
            ·
              refine ⟨6732215091899109648503893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35905147156795251458687429 6732215091899109648503893)
              ·
                refine ⟨78893145608192691193405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6732215091899109648503893 78893145608192691193405)
                ·
                  rfl

theorem cell23_4148384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 8].length) (baseStart_4148384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148384 prefixEnd_4148384 := by exact prefixLift 4148384
  have htrace : WordTrace (prefixWord ++ tailWord_4148384) baseStart_4148384 baseEnd_4148384 := by
    simpa [prefixWord, tailWord_4148384, baseEnd_4148384] using wordTrace_append hprefix tailTrace_4148384
  have hstable : (prefixWord ++ tailWord_4148384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148384).length < 2 ^ (prefixWord ++ tailWord_4148384).sum := by decide
  have hdescent : baseEnd_4148384 < baseStart_4148384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148388 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 2, 4]
def baseStart_4148388 : Nat := 118140960795 + 4148388 * 2 ^ 59
def prefixEnd_4148388 : Nat := 4983230072969 + 3 ^ 40 * 4148388 * 2
def baseEnd_4148388 : Nat := 710038995114606882190639

theorem tailTrace_4148388 : CollatzResearch.WordTrace tailWord_4148388 prefixEnd_4148388 710038995114606882190639 := by
  unfold tailWord_4148388
  simp only [CollatzResearch.WordTrace]
  refine ⟨75652070247553119554938909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100869426996737492739918545 75652070247553119554938909)
  ·
    refine ⟨28369526342832419833102091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75652070247553119554938909 28369526342832419833102091)
    ·
      refine ⟨42554289514248629749653137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28369526342832419833102091 42554289514248629749653137)
      ·
        refine ⟨31915717135686472312239853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42554289514248629749653137 31915717135686472312239853)
        ·
          refine ⟨11968393925882427117089945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31915717135686472312239853 11968393925882427117089945)
          ·
            refine ⟨8976295444411820337817459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11968393925882427117089945 8976295444411820337817459)
            ·
              refine ⟨13464443166617730506726189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8976295444411820337817459 13464443166617730506726189)
              ·
                refine ⟨5049166187481648940022321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13464443166617730506726189 5049166187481648940022321)
                ·
                  refine ⟨3786874640611236705016741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049166187481648940022321 3786874640611236705016741)
                  ·
                    refine ⟨710038995114606882190639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3786874640611236705016741 710038995114606882190639)
                    ·
                      rfl

theorem cell23_4148388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 4].length) (baseStart_4148388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148388 prefixEnd_4148388 := by exact prefixLift 4148388
  have htrace : WordTrace (prefixWord ++ tailWord_4148388) baseStart_4148388 baseEnd_4148388 := by
    simpa [prefixWord, tailWord_4148388, baseEnd_4148388] using wordTrace_append hprefix tailTrace_4148388
  have hstable : (prefixWord ++ tailWord_4148388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148388).length < 2 ^ (prefixWord ++ tailWord_4148388).sum := by decide
  have hdescent : baseEnd_4148388 < baseStart_4148388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148391 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4148391 : Nat := 118140960795 + 4148391 * 2 ^ 59
def prefixEnd_4148391 : Nat := 4983230072969 + 3 ^ 40 * 4148391 * 2
def baseEnd_4148391 : Nat := 2130118525785784134834403

theorem tailTrace_4148391 : CollatzResearch.WordTrace tailWord_4148391 prefixEnd_4148391 2130118525785784134834403 := by
  unfold tailWord_4148391
  simp only [CollatzResearch.WordTrace]
  refine ⟨151304249914095370622237027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100869499942730247081491351 151304249914095370622237027)
  ·
    refine ⟨226956374871143055933355541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151304249914095370622237027 226956374871143055933355541)
    ·
      refine ⟨10638580072084830746876041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 226956374871143055933355541 10638580072084830746876041)
      ·
        refine ⟨7978935054063623060157031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10638580072084830746876041 7978935054063623060157031)
        ·
          refine ⟨11968402581095434590235547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7978935054063623060157031 11968402581095434590235547)
          ·
            refine ⟨17952603871643151885353321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968402581095434590235547 17952603871643151885353321)
            ·
              refine ⟨13464452903732363914014991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17952603871643151885353321 13464452903732363914014991)
              ·
                refine ⟨20196679355598545871022487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13464452903732363914014991 20196679355598545871022487)
                ·
                  refine ⟨30295019033397818806533731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20196679355598545871022487 30295019033397818806533731)
                  ·
                    refine ⟨45442528550096728209800597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30295019033397818806533731 45442528550096728209800597)
                    ·
                      refine ⟨2130118525785784134834403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45442528550096728209800597 2130118525785784134834403)
                      ·
                        rfl

theorem cell23_4148391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4148391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148391 prefixEnd_4148391 := by exact prefixLift 4148391
  have htrace : WordTrace (prefixWord ++ tailWord_4148391) baseStart_4148391 baseEnd_4148391 := by
    simpa [prefixWord, tailWord_4148391, baseEnd_4148391] using wordTrace_append hprefix tailTrace_4148391
  have hstable : (prefixWord ++ tailWord_4148391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148391).length < 2 ^ (prefixWord ++ tailWord_4148391).sum := by decide
  have hdescent : baseEnd_4148391 < baseStart_4148391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148411 : List Nat := [1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 3]
def baseStart_4148411 : Nat := 118140960795 + 4148411 * 2 ^ 59
def prefixEnd_4148411 : Nat := 4983230072969 + 3 ^ 40 * 4148411 * 2
def baseEnd_4148411 : Nat := 2130128795398874056584311

theorem tailTrace_4148411 : CollatzResearch.WordTrace tailWord_4148411 prefixEnd_4148411 2130128795398874056584311 := by
  unfold tailWord_4148411
  simp only [CollatzResearch.WordTrace]
  refine ⟨151304979374022914037965087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100869986249348609358643391 151304979374022914037965087)
  ·
    refine ⟨226957469061034371056947631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151304979374022914037965087 226957469061034371056947631)
    ·
      refine ⟨340436203591551556585421447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226957469061034371056947631 340436203591551556585421447)
      ·
        refine ⟨510654305387327334878132171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340436203591551556585421447 510654305387327334878132171)
        ·
          refine ⟨765981458080991002317198257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510654305387327334878132171 765981458080991002317198257)
          ·
            refine ⟨574486093560743251737898693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765981458080991002317198257 574486093560743251737898693)
            ·
              refine ⟨107716142542639359700856005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 574486093560743251737898693 107716142542639359700856005)
              ·
                refine ⟨20196776726744879943910501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107716142542639359700856005 20196776726744879943910501)
                ·
                  refine ⟨3786895636264664989483219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20196776726744879943910501 3786895636264664989483219)
                  ·
                    refine ⟨5680343454396997484224829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3786895636264664989483219 5680343454396997484224829)
                    ·
                      refine ⟨2130128795398874056584311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5680343454396997484224829 2130128795398874056584311)
                      ·
                        rfl

theorem cell23_4148411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 1, 3].length) (baseStart_4148411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148411 prefixEnd_4148411 := by exact prefixLift 4148411
  have htrace : WordTrace (prefixWord ++ tailWord_4148411) baseStart_4148411 baseEnd_4148411 := by
    simpa [prefixWord, tailWord_4148411, baseEnd_4148411] using wordTrace_append hprefix tailTrace_4148411
  have hstable : (prefixWord ++ tailWord_4148411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148411).length < 2 ^ (prefixWord ++ tailWord_4148411).sum := by decide
  have hdescent : baseEnd_4148411 < baseStart_4148411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148418 : List Nat := [3, 5, 1, 1, 2, 11]
def baseStart_4148418 : Nat := 118140960795 + 4148418 * 2 ^ 59
def prefixEnd_4148418 : Nat := 4983230072969 + 3 ^ 40 * 4148418 * 2
def baseEnd_4148418 : Nat := 8765976912606812877353

theorem tailTrace_4148418 : CollatzResearch.WordTrace tailWord_4148418 prefixEnd_4148418 8765976912606812877353 := by
  unfold tailWord_4148418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37826308671249388558367477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100870156456665036155646605 37826308671249388558367477)
  ·
    refine ⟨3546216437929630177346951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37826308671249388558367477 3546216437929630177346951)
    ·
      refine ⟨5319324656894445266020427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546216437929630177346951 5319324656894445266020427)
      ·
        refine ⟨7978986985341667899030641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319324656894445266020427 7978986985341667899030641)
        ·
          refine ⟨5984240239006250924272981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7978986985341667899030641 5984240239006250924272981)
          ·
            refine ⟨8765976912606812877353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5984240239006250924272981 8765976912606812877353)
            ·
              rfl

theorem cell23_4148418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 11].length) (baseStart_4148418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148418 prefixEnd_4148418 := by exact prefixLift 4148418
  have htrace : WordTrace (prefixWord ++ tailWord_4148418) baseStart_4148418 baseEnd_4148418 := by
    simpa [prefixWord, tailWord_4148418, baseEnd_4148418] using wordTrace_append hprefix tailTrace_4148418
  have hstable : (prefixWord ++ tailWord_4148418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148418).length < 2 ^ (prefixWord ++ tailWord_4148418).sum := by decide
  have hdescent : baseEnd_4148418 < baseStart_4148418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148424 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_4148424 : Nat := 118140960795 + 4148424 * 2 ^ 59
def prefixEnd_4148424 : Nat := 4983230072969 + 3 ^ 40 * 4148424 * 2
def baseEnd_4148424 : Nat := 2130135470647382505721751

theorem tailTrace_4148424 : CollatzResearch.WordTrace tailWord_4148424 prefixEnd_4148424 2130135470647382505721751 := by
  unfold tailWord_4148424
  simp only [CollatzResearch.WordTrace]
  refine ⟨75652726761487908629094163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100870302348650544838792217 75652726761487908629094163)
  ·
    refine ⟨113479090142231862943641245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75652726761487908629094163 113479090142231862943641245)
    ·
      refine ⟨42554658803336948603865467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113479090142231862943641245 42554658803336948603865467)
      ·
        refine ⟨63831988205005422905798201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42554658803336948603865467 63831988205005422905798201)
        ·
          refine ⟨47873991153754067179348651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63831988205005422905798201 47873991153754067179348651)
          ·
            refine ⟨71810986730631100769022977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47873991153754067179348651 71810986730631100769022977)
            ·
              refine ⟨53858240047973325576767233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71810986730631100769022977 53858240047973325576767233)
              ·
                refine ⟨40393680035979994182575425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53858240047973325576767233 40393680035979994182575425)
                ·
                  refine ⟨30295260026984995636931569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40393680035979994182575425 30295260026984995636931569)
                  ·
                    refine ⟨22721445020238746727698677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30295260026984995636931569 22721445020238746727698677)
                    ·
                      refine ⟨2130135470647382505721751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22721445020238746727698677 2130135470647382505721751)
                      ·
                        rfl

theorem cell23_4148424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_4148424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148424 prefixEnd_4148424 := by exact prefixLift 4148424
  have htrace : WordTrace (prefixWord ++ tailWord_4148424) baseStart_4148424 baseEnd_4148424 := by
    simpa [prefixWord, tailWord_4148424, baseEnd_4148424] using wordTrace_append hprefix tailTrace_4148424
  have hstable : (prefixWord ++ tailWord_4148424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148424).length < 2 ^ (prefixWord ++ tailWord_4148424).sum := by decide
  have hdescent : baseEnd_4148424 < baseStart_4148424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148445 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4148445 : Nat := 118140960795 + 4148445 * 2 ^ 59
def prefixEnd_4148445 : Nat := 4983230072969 + 3 ^ 40 * 4148445 * 2
def baseEnd_4148445 : Nat := 2130146253741126923559155

theorem tailTrace_4148445 : CollatzResearch.WordTrace tailWord_4148445 prefixEnd_4148445 2130146253741126923559155 := by
  unfold tailWord_4148445
  simp only [CollatzResearch.WordTrace]
  refine ⟨151306219455899737844702789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100870812970599825229801859 151306219455899737844702789)
  ·
    refine ⟨28369916147981200845881773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151306219455899737844702789 28369916147981200845881773)
    ·
      refine ⟨10638718555492950317205665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28369916147981200845881773 10638718555492950317205665)
      ·
        refine ⟨7979038916619712737904249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10638718555492950317205665 7979038916619712737904249)
        ·
          refine ⟨5984279187464784553428187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7979038916619712737904249 5984279187464784553428187)
          ·
            refine ⟨8976418781197176830142281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984279187464784553428187 8976418781197176830142281)
            ·
              refine ⟨6732314085897882622606711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8976418781197176830142281 6732314085897882622606711)
              ·
                refine ⟨10098471128846823933910067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732314085897882622606711 10098471128846823933910067)
                ·
                  refine ⟨15147706693270235900865101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10098471128846823933910067 15147706693270235900865101)
                  ·
                    refine ⟨5680390009976338462824413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15147706693270235900865101 5680390009976338462824413)
                    ·
                      refine ⟨2130146253741126923559155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5680390009976338462824413 2130146253741126923559155)
                      ·
                        rfl

theorem cell23_4148445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4148445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148445 prefixEnd_4148445 := by exact prefixLift 4148445
  have htrace : WordTrace (prefixWord ++ tailWord_4148445) baseStart_4148445 baseEnd_4148445 := by
    simpa [prefixWord, tailWord_4148445, baseEnd_4148445] using wordTrace_append hprefix tailTrace_4148445
  have hstable : (prefixWord ++ tailWord_4148445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148445).length < 2 ^ (prefixWord ++ tailWord_4148445).sum := by decide
  have hdescent : baseEnd_4148445 < baseStart_4148445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148474 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_4148474 : Nat := 118140960795 + 4148474 * 2 ^ 59
def prefixEnd_4148474 : Nat := 4983230072969 + 3 ^ 40 * 4148474 * 2
def baseEnd_4148474 : Nat := 236684571631123034455169

theorem tailTrace_4148474 : CollatzResearch.WordTrace tailWord_4148474 prefixEnd_4148474 236684571631123034455169 := by
  unfold tailWord_4148474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37826819293198668949377119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100871518115196450531672317 37826819293198668949377119)
  ·
    refine ⟨56740228939798003424065679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37826819293198668949377119 56740228939798003424065679)
    ·
      refine ⟨85110343409697005136098519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56740228939798003424065679 85110343409697005136098519)
      ·
        refine ⟨127665515114545507704147779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85110343409697005136098519 127665515114545507704147779)
        ·
          refine ⟨191498272671818261556221669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127665515114545507704147779 191498272671818261556221669)
          ·
            refine ⟨35905926125965924041791563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191498272671818261556221669 35905926125965924041791563)
            ·
              refine ⟨53858889188948886062687345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35905926125965924041791563 53858889188948886062687345)
              ·
                refine ⟨40394166891711664547015509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53858889188948886062687345 40394166891711664547015509)
                ·
                  refine ⟨236684571631123034455169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40394166891711664547015509 236684571631123034455169)
                  ·
                    rfl

theorem cell23_4148474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_4148474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148474 prefixEnd_4148474 := by exact prefixLift 4148474
  have htrace : WordTrace (prefixWord ++ tailWord_4148474) baseStart_4148474 baseEnd_4148474 := by
    simpa [prefixWord, tailWord_4148474, baseEnd_4148474] using wordTrace_append hprefix tailTrace_4148474
  have hstable : (prefixWord ++ tailWord_4148474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148474).length < 2 ^ (prefixWord ++ tailWord_4148474).sum := by decide
  have hdescent : baseEnd_4148474 < baseStart_4148474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148481 : List Nat := [1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4148481 : Nat := 118140960795 + 4148481 * 2 ^ 59
def prefixEnd_4148481 : Nat := 4983230072969 + 3 ^ 40 * 4148481 * 2
def baseEnd_4148481 : Nat := 2130164739044688782708989

theorem tailTrace_4148481 : CollatzResearch.WordTrace tailWord_4148481 prefixEnd_4148481 2130164739044688782708989 := by
  unfold tailWord_4148481
  simp only [CollatzResearch.WordTrace]
  refine ⟨151307532483769315993013297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100871688322512877328675531 151307532483769315993013297)
  ·
    refine ⟨113480649362826986994759973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151307532483769315993013297 113480649362826986994759973)
    ·
      refine ⟨21277621755530060061517495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113480649362826986994759973 21277621755530060061517495)
      ·
        refine ⟨31916432633295090092276243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21277621755530060061517495 31916432633295090092276243)
        ·
          refine ⟨47874648949942635138414365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31916432633295090092276243 47874648949942635138414365)
          ·
            refine ⟨17952993356228488176905387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47874648949942635138414365 17952993356228488176905387)
            ·
              refine ⟨26929490034342732265358081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17952993356228488176905387 26929490034342732265358081)
              ·
                refine ⟨20197117525757049199018561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26929490034342732265358081 20197117525757049199018561)
                ·
                  refine ⟨15147838144317786899263921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20197117525757049199018561 15147838144317786899263921)
                  ·
                    refine ⟨11360878608238340174447941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15147838144317786899263921 11360878608238340174447941)
                    ·
                      refine ⟨2130164739044688782708989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11360878608238340174447941 2130164739044688782708989)
                      ·
                        rfl

theorem cell23_4148481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4148481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148481 prefixEnd_4148481 := by exact prefixLift 4148481
  have htrace : WordTrace (prefixWord ++ tailWord_4148481) baseStart_4148481 baseEnd_4148481 := by
    simpa [prefixWord, tailWord_4148481, baseEnd_4148481] using wordTrace_append hprefix tailTrace_4148481
  have hstable : (prefixWord ++ tailWord_4148481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148481).length < 2 ^ (prefixWord ++ tailWord_4148481).sum := by decide
  have hdescent : baseEnd_4148481 < baseStart_4148481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148491 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 7]
def baseStart_4148491 : Nat := 118140960795 + 4148491 * 2 ^ 59
def prefixEnd_4148491 : Nat := 4983230072969 + 3 ^ 40 * 4148491 * 2
def baseEnd_4148491 : Nat := 236685541539025971509327

theorem tailTrace_4148491 : CollatzResearch.WordTrace tailWord_4148491 prefixEnd_4148491 236685541539025971509327 := by
  unfold tailWord_4148491
  simp only [CollatzResearch.WordTrace]
  refine ⟨151307897213733087700877327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100871931475822058467251551 151307897213733087700877327)
  ·
    refine ⟨226961845820599631551315991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151307897213733087700877327 226961845820599631551315991)
    ·
      refine ⟨340442768730899447326973987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226961845820599631551315991 340442768730899447326973987)
      ·
        refine ⟨510664153096349170990460981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340442768730899447326973987 510664153096349170990460981)
        ·
          refine ⟨47874764352782734780355717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510664153096349170990460981 47874764352782734780355717)
          ·
            refine ⟨8976518316146762771316697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47874764352782734780355717 8976518316146762771316697)
            ·
              refine ⟨6732388737110072078487523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8976518316146762771316697 6732388737110072078487523)
              ·
                refine ⟨10098583105665108117731285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732388737110072078487523 10098583105665108117731285)
                ·
                  refine ⟨236685541539025971509327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10098583105665108117731285 236685541539025971509327)
                  ·
                    rfl

theorem cell23_4148491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 7].length) (baseStart_4148491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148491 prefixEnd_4148491 := by exact prefixLift 4148491
  have htrace : WordTrace (prefixWord ++ tailWord_4148491) baseStart_4148491 baseEnd_4148491 := by
    simpa [prefixWord, tailWord_4148491, baseEnd_4148491] using wordTrace_append hprefix tailTrace_4148491
  have hstable : (prefixWord ++ tailWord_4148491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148491).length < 2 ^ (prefixWord ++ tailWord_4148491).sum := by decide
  have hdescent : baseEnd_4148491 < baseStart_4148491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148548 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4148548 : Nat := 118140960795 + 4148548 * 2 ^ 59
def prefixEnd_4148548 : Nat := 4983230072969 + 3 ^ 40 * 4148548 * 2
def baseEnd_4148548 : Nat := 2130199142248540020571181

theorem tailTrace_4148548 : CollatzResearch.WordTrace tailWord_4148548 prefixEnd_4148548 2130199142248540020571181 := by
  unfold tailWord_4148548
  simp only [CollatzResearch.WordTrace]
  refine ⟨75654988087263293217851149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100873317449684390957134865 75654988087263293217851149)
  ·
    refine ⟨28370620532723734956694181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75654988087263293217851149 28370620532723734956694181)
    ·
      refine ⟨5319491349885700304380159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28370620532723734956694181 5319491349885700304380159)
      ·
        refine ⟨7979237024828550456570239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5319491349885700304380159 7979237024828550456570239)
        ·
          refine ⟨11968855537242825684855359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7979237024828550456570239 11968855537242825684855359)
          ·
            refine ⟨17953283305864238527283039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11968855537242825684855359 17953283305864238527283039)
            ·
              refine ⟨26929924958796357790924559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17953283305864238527283039 26929924958796357790924559)
              ·
                refine ⟨40394887438194536686386839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26929924958796357790924559 40394887438194536686386839)
                ·
                  refine ⟨60592331157291805029580259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40394887438194536686386839 60592331157291805029580259)
                  ·
                    refine ⟨90888496735937707544370389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60592331157291805029580259 90888496735937707544370389)
                    ·
                      refine ⟨2130199142248540020571181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 90888496735937707544370389 2130199142248540020571181)
                      ·
                        rfl

theorem cell23_4148548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4148548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148548 prefixEnd_4148548 := by exact prefixLift 4148548
  have htrace : WordTrace (prefixWord ++ tailWord_4148548) baseStart_4148548 baseEnd_4148548 := by
    simpa [prefixWord, tailWord_4148548, baseEnd_4148548] using wordTrace_append hprefix tailTrace_4148548
  have hstable : (prefixWord ++ tailWord_4148548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148548).length < 2 ^ (prefixWord ++ tailWord_4148548).sum := by decide
  have hdescent : baseEnd_4148548 < baseStart_4148548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148558 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_4148558 : Nat := 118140960795 + 4148558 * 2 ^ 59
def prefixEnd_4148558 : Nat := 4983230072969 + 3 ^ 40 * 4148558 * 2
def baseEnd_4148558 : Nat := 2130204277055084981446135

theorem tailTrace_4148558 : CollatzResearch.WordTrace tailWord_4148558 prefixEnd_4148558 2130204277055084981446135 := by
  unfold tailWord_4148558
  simp only [CollatzResearch.WordTrace]
  refine ⟨18913792613061294767945791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100873560602993572095710885 18913792613061294767945791)
  ·
    refine ⟨28370688919591942151918687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18913792613061294767945791 28370688919591942151918687)
    ·
      refine ⟨42556033379387913227878031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28370688919591942151918687 42556033379387913227878031)
      ·
        refine ⟨63834050069081869841817047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42556033379387913227878031 63834050069081869841817047)
        ·
          refine ⟨95751075103622804762725571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63834050069081869841817047 95751075103622804762725571)
          ·
            refine ⟨143626612655434207144088357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95751075103622804762725571 143626612655434207144088357)
            ·
              refine ⟨26929989872893913839516567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143626612655434207144088357 26929989872893913839516567)
              ·
                refine ⟨40394984809340870759274851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26929989872893913839516567 40394984809340870759274851)
                ·
                  refine ⟨60592477214011306138912277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40394984809340870759274851 60592477214011306138912277)
                  ·
                    refine ⟨2840272369406779975261513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 60592477214011306138912277 2840272369406779975261513)
                    ·
                      refine ⟨2130204277055084981446135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2840272369406779975261513 2130204277055084981446135)
                      ·
                        rfl

theorem cell23_4148558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_4148558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148558 prefixEnd_4148558 := by exact prefixLift 4148558
  have htrace : WordTrace (prefixWord ++ tailWord_4148558) baseStart_4148558 baseEnd_4148558 := by
    simpa [prefixWord, tailWord_4148558, baseEnd_4148558] using wordTrace_append hprefix tailTrace_4148558
  have hstable : (prefixWord ++ tailWord_4148558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148558).length < 2 ^ (prefixWord ++ tailWord_4148558).sum := by decide
  have hdescent : baseEnd_4148558 < baseStart_4148558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148608 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 7, 1, 3]
def baseStart_4148608 : Nat := 118140960795 + 4148608 * 2 ^ 59
def prefixEnd_4148608 : Nat := 4983230072969 + 3 ^ 40 * 4148608 * 2
def baseEnd_4148608 : Nat := 2130229951087809785820905

theorem tailTrace_4148608 : CollatzResearch.WordTrace tailWord_4148608 prefixEnd_4148608 2130229951087809785820905 := by
  unfold tailWord_4148608
  simp only [CollatzResearch.WordTrace]
  refine ⟨75656082277154608341443239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100874776369539477788590985 75656082277154608341443239)
  ·
    refine ⟨113484123415731912512164859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75656082277154608341443239 113484123415731912512164859)
    ·
      refine ⟨170226185123597868768247289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113484123415731912512164859 170226185123597868768247289)
      ·
        refine ⟨127669638842698401576185467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170226185123597868768247289 127669638842698401576185467)
        ·
          refine ⟨191504458264047602364278201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127669638842698401576185467 191504458264047602364278201)
          ·
            refine ⟨143628343698035701773208651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191504458264047602364278201 143628343698035701773208651)
            ·
              refine ⟨215442515547053552659812977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143628343698035701773208651 215442515547053552659812977)
              ·
                refine ⟨161581886660290164494859733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215442515547053552659812977 161581886660290164494859733)
                ·
                  refine ⟨3787075468600550730348275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 161581886660290164494859733 3787075468600550730348275)
                  ·
                    refine ⟨5680613202900826095522413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787075468600550730348275 5680613202900826095522413)
                    ·
                      refine ⟨2130229951087809785820905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5680613202900826095522413 2130229951087809785820905)
                      ·
                        rfl

theorem cell23_4148608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 7, 1, 3].length) (baseStart_4148608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148608 prefixEnd_4148608 := by exact prefixLift 4148608
  have htrace : WordTrace (prefixWord ++ tailWord_4148608) baseStart_4148608 baseEnd_4148608 := by
    simpa [prefixWord, tailWord_4148608, baseEnd_4148608] using wordTrace_append hprefix tailTrace_4148608
  have hstable : (prefixWord ++ tailWord_4148608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148608).length < 2 ^ (prefixWord ++ tailWord_4148608).sum := by decide
  have hdescent : baseEnd_4148608 < baseStart_4148608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148682 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2]
def baseStart_4148682 : Nat := 118140960795 + 4148682 * 2 ^ 59
def prefixEnd_4148682 : Nat := 4983230072969 + 3 ^ 40 * 4148682 * 2
def baseEnd_4148682 : Nat := 2130267948656242496295565

theorem tailTrace_4148682 : CollatzResearch.WordTrace tailWord_4148682 prefixEnd_4148682 2130267948656242496295565 := by
  unfold tailWord_4148682
  simp only [CollatzResearch.WordTrace]
  refine ⟨37828715889010281830270075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100876575704027418214053533 37828715889010281830270075)
  ·
    refine ⟨56743073833515422745405113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37828715889010281830270075 56743073833515422745405113)
    ·
      refine ⟨42557305375136567059053835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56743073833515422745405113 42557305375136567059053835)
      ·
        refine ⟨63835958062704850588580753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42557305375136567059053835 63835958062704850588580753)
        ·
          refine ⟨47876968547028637941435565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63835958062704850588580753 47876968547028637941435565)
          ·
            refine ⟨17953863205135739228038337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47876968547028637941435565 17953863205135739228038337)
            ·
              refine ⟨13465397403851804421028753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17953863205135739228038337 13465397403851804421028753)
              ·
                refine ⟨10099048052888853315771565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13465397403851804421028753 10099048052888853315771565)
                ·
                  refine ⟨3787143019833319993414337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10099048052888853315771565 3787143019833319993414337)
                  ·
                    refine ⟨2840357264874989995060753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3787143019833319993414337 2840357264874989995060753)
                    ·
                      refine ⟨2130267948656242496295565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2840357264874989995060753 2130267948656242496295565)
                      ·
                        rfl

theorem cell23_4148682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_4148682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148682 prefixEnd_4148682 := by exact prefixLift 4148682
  have htrace : WordTrace (prefixWord ++ tailWord_4148682) baseStart_4148682 baseEnd_4148682 := by
    simpa [prefixWord, tailWord_4148682, baseEnd_4148682] using wordTrace_append hprefix tailTrace_4148682
  have hstable : (prefixWord ++ tailWord_4148682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148682).length < 2 ^ (prefixWord ++ tailWord_4148682).sum := by decide
  have hdescent : baseEnd_4148682 < baseStart_4148682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148718 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4148718 : Nat := 118140960795 + 4148718 * 2 ^ 59
def prefixEnd_4148718 : Nat := 4983230072969 + 3 ^ 40 * 4148718 * 2
def baseEnd_4148718 : Nat := 710095477986601451815133

theorem tailTrace_4148718 : CollatzResearch.WordTrace tailWord_4148718 prefixEnd_4148718 710095477986601451815133 := by
  unfold tailWord_4148718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18914522072988838183673851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100877451055940470312927205 18914522072988838183673851)
  ·
    refine ⟨28371783109483257275510777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18914522072988838183673851 28371783109483257275510777)
    ·
      refine ⟨21278837332112442956633083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28371783109483257275510777 21278837332112442956633083)
      ·
        refine ⟨31918255998168664434949625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21278837332112442956633083 31918255998168664434949625)
        ·
          refine ⟨23938691998626498326212219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31918255998168664434949625 23938691998626498326212219)
          ·
            refine ⟨35908037997939747489318329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23938691998626498326212219 35908037997939747489318329)
            ·
              refine ⟨26931028498454810616988747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35908037997939747489318329 26931028498454810616988747)
              ·
                refine ⟨40396542747682215925483121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26931028498454810616988747 40396542747682215925483121)
                ·
                  refine ⟨30297407060761661944112341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40396542747682215925483121 30297407060761661944112341)
                  ·
                    refine ⟨710095477986601451815133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30297407060761661944112341 710095477986601451815133)
                    ·
                      rfl

theorem cell23_4148718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4148718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148718 prefixEnd_4148718 := by exact prefixLift 4148718
  have htrace : WordTrace (prefixWord ++ tailWord_4148718) baseStart_4148718 baseEnd_4148718 := by
    simpa [prefixWord, tailWord_4148718, baseEnd_4148718] using wordTrace_append hprefix tailTrace_4148718
  have hstable : (prefixWord ++ tailWord_4148718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148718).length < 2 ^ (prefixWord ++ tailWord_4148718).sum := by decide
  have hdescent : baseEnd_4148718 < baseStart_4148718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148755 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 3, 4, 2]
def baseStart_4148755 : Nat := 118140960795 + 4148755 * 2 ^ 59
def prefixEnd_4148755 : Nat := 4983230072969 + 3 ^ 40 * 4148755 * 2
def baseEnd_4148755 : Nat := 2130305432744020710682729

theorem tailTrace_4148755 : CollatzResearch.WordTrace tailWord_4148755 prefixEnd_4148755 2130305432744020710682729 := by
  unfold tailWord_4148755
  simp only [CollatzResearch.WordTrace]
  refine ⟨151317526084776660788487719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100878350723184440525658479 151317526084776660788487719)
  ·
    refine ⟨226976289127164991182731579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151317526084776660788487719 226976289127164991182731579)
    ·
      refine ⟨340464433690747486774097369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226976289127164991182731579 340464433690747486774097369)
      ·
        refine ⟨255348325268060615080573027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340464433690747486774097369 255348325268060615080573027)
        ·
          refine ⟨383022487902090922620859541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255348325268060615080573027 383022487902090922620859541)
          ·
            refine ⟨17954179120410511997852791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 383022487902090922620859541 17954179120410511997852791)
            ·
              refine ⟨26931268680615767996779187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17954179120410511997852791 26931268680615767996779187)
              ·
                refine ⟨40396903020923651995168781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26931268680615767996779187 40396903020923651995168781)
                ·
                  refine ⟨15148838632846369498188293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40396903020923651995168781 15148838632846369498188293)
                  ·
                    refine ⟨2840407243658694280910305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15148838632846369498188293 2840407243658694280910305)
                    ·
                      refine ⟨2130305432744020710682729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2840407243658694280910305 2130305432744020710682729)
                      ·
                        rfl

theorem cell23_4148755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4, 2].length) (baseStart_4148755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148755 prefixEnd_4148755 := by exact prefixLift 4148755
  have htrace : WordTrace (prefixWord ++ tailWord_4148755) baseStart_4148755 baseEnd_4148755 := by
    simpa [prefixWord, tailWord_4148755, baseEnd_4148755] using wordTrace_append hprefix tailTrace_4148755
  have hstable : (prefixWord ++ tailWord_4148755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148755).length < 2 ^ (prefixWord ++ tailWord_4148755).sum := by decide
  have hdescent : baseEnd_4148755 < baseStart_4148755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148789 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 2, 2, 2]
def baseStart_4148789 : Nat := 118140960795 + 4148789 * 2 ^ 59
def prefixEnd_4148789 : Nat := 4983230072969 + 3 ^ 40 * 4148789 * 2
def baseEnd_4148789 : Nat := 2130322891086273577657573

theorem tailTrace_4148789 : CollatzResearch.WordTrace tailWord_4148789 prefixEnd_4148789 2130322891086273577657573 := by
  unfold tailWord_4148789
  simp only [CollatzResearch.WordTrace]
  refine ⟨151318766166653484595225421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100879177444435656396816947 151318766166653484595225421)
  ·
    refine ⟨56744537312495056723209533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151318766166653484595225421 56744537312495056723209533)
    ·
      refine ⟨21279201492185646271203575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56744537312495056723209533 21279201492185646271203575)
      ·
        refine ⟨31918802238278469406805363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21279201492185646271203575 31918802238278469406805363)
        ·
          refine ⟨47878203357417704110208045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31918802238278469406805363 47878203357417704110208045)
          ·
            refine ⟨17954326259031639041328017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47878203357417704110208045 17954326259031639041328017)
            ·
              refine ⟨13465744694273729280996013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17954326259031639041328017 13465744694273729280996013)
              ·
                refine ⟨5049654260352648480373505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13465744694273729280996013 5049654260352648480373505)
                ·
                  refine ⟨3787240695264486360280129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049654260352648480373505 3787240695264486360280129)
                  ·
                    refine ⟨2840430521448364770210097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3787240695264486360280129 2840430521448364770210097)
                    ·
                      refine ⟨2130322891086273577657573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2840430521448364770210097 2130322891086273577657573)
                      ·
                        rfl

theorem cell23_4148789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_4148789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148789 prefixEnd_4148789 := by exact prefixLift 4148789
  have htrace : WordTrace (prefixWord ++ tailWord_4148789) baseStart_4148789 baseEnd_4148789 := by
    simpa [prefixWord, tailWord_4148789, baseEnd_4148789] using wordTrace_append hprefix tailTrace_4148789
  have hstable : (prefixWord ++ tailWord_4148789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148789).length < 2 ^ (prefixWord ++ tailWord_4148789).sum := by decide
  have hdescent : baseEnd_4148789 < baseStart_4148789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148812 : List Nat := [2, 2, 1, 3, 1, 4, 2, 3, 5]
def baseStart_4148812 : Nat := 118140960795 + 4148812 * 2 ^ 59
def prefixEnd_4148812 : Nat := 4983230072969 + 3 ^ 40 * 4148812 * 2
def baseEnd_4148812 : Nat := 236703855682369665296663

theorem tailTrace_4148812 : CollatzResearch.WordTrace tailWord_4148812 prefixEnd_4148812 236703855682369665296663 := by
  unfold tailWord_4148812
  simp only [CollatzResearch.WordTrace]
  refine ⟨75659802522785079761656345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100879736697046773015541793 75659802522785079761656345)
  ·
    refine ⟨56744851892088809821242259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75659802522785079761656345 56744851892088809821242259)
    ·
      refine ⟨85117277838133214731863389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56744851892088809821242259 85117277838133214731863389)
      ·
        refine ⟨31918979189299955524448771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85117277838133214731863389 31918979189299955524448771)
        ·
          refine ⟨47878468783949933286673157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31918979189299955524448771 47878468783949933286673157)
          ·
            refine ⟨8977212896990612491251217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47878468783949933286673157 8977212896990612491251217)
            ·
              refine ⟨6732909672742959368438413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8977212896990612491251217 6732909672742959368438413)
              ·
                refine ⟨2524841127278609763164405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6732909672742959368438413 2524841127278609763164405)
                ·
                  refine ⟨236703855682369665296663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2524841127278609763164405 236703855682369665296663)
                  ·
                    rfl

theorem cell23_4148812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_4148812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148812 prefixEnd_4148812 := by exact prefixLift 4148812
  have htrace : WordTrace (prefixWord ++ tailWord_4148812) baseStart_4148812 baseEnd_4148812 := by
    simpa [prefixWord, tailWord_4148812, baseEnd_4148812] using wordTrace_append hprefix tailTrace_4148812
  have hstable : (prefixWord ++ tailWord_4148812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148812).length < 2 ^ (prefixWord ++ tailWord_4148812).sum := by decide
  have hdescent : baseEnd_4148812 < baseStart_4148812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148829 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 7]
def baseStart_4148829 : Nat := 118140960795 + 4148829 * 2 ^ 59
def prefixEnd_4148829 : Nat := 4983230072969 + 3 ^ 40 * 4148829 * 2
def baseEnd_4148829 : Nat := 236704825590272602350821

theorem tailTrace_4148829 : CollatzResearch.WordTrace tailWord_4148829 prefixEnd_4148829 236704825590272602350821 := by
  unfold tailWord_4148829
  simp only [CollatzResearch.WordTrace]
  refine ⟨151320225086508571426681541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100880150057672380951121027 151320225086508571426681541)
  ·
    refine ⟨28372542203720357142502789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151320225086508571426681541 28372542203720357142502789)
    ·
      refine ⟨5319851663197566964219273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28372542203720357142502789 5319851663197566964219273)
      ·
        refine ⟨3989888747398175223164455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5319851663197566964219273 3989888747398175223164455)
        ·
          refine ⟨5984833121097262834746683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3989888747398175223164455 5984833121097262834746683)
          ·
            refine ⟨8977249681645894252120025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5984833121097262834746683 8977249681645894252120025)
            ·
              refine ⟨6732937261234420689090019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8977249681645894252120025 6732937261234420689090019)
              ·
                refine ⟨10099405891851631033635029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6732937261234420689090019 10099405891851631033635029)
                ·
                  refine ⟨236704825590272602350821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10099405891851631033635029 236704825590272602350821)
                  ·
                    rfl

theorem cell23_4148829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_4148829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148829 prefixEnd_4148829 := by exact prefixLift 4148829
  have htrace : WordTrace (prefixWord ++ tailWord_4148829) baseStart_4148829 baseEnd_4148829 := by
    simpa [prefixWord, tailWord_4148829, baseEnd_4148829] using wordTrace_append hprefix tailTrace_4148829
  have hstable : (prefixWord ++ tailWord_4148829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148829).length < 2 ^ (prefixWord ++ tailWord_4148829).sum := by decide
  have hdescent : baseEnd_4148829 < baseStart_4148829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148858 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6]
def baseStart_4148858 : Nat := 118140960795 + 4148858 * 2 ^ 59
def prefixEnd_4148858 : Nat := 4983230072969 + 3 ^ 40 * 4148858 * 2
def baseEnd_4148858 : Nat := 2130358321251433807694755

theorem tailTrace_4148858 : CollatzResearch.WordTrace tailWord_4148858 prefixEnd_4148858 2130358321251433807694755 := by
  unfold tailWord_4148858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37830320700850877344871807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100880855202269006252991485 37830320700850877344871807)
  ·
    refine ⟨56745481051276316017307711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37830320700850877344871807 56745481051276316017307711)
    ·
      refine ⟨85118221576914474025961567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56745481051276316017307711 85118221576914474025961567)
      ·
        refine ⟨127677332365371711038942351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85118221576914474025961567 127677332365371711038942351)
        ·
          refine ⟨191515998548057566558413527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127677332365371711038942351 191515998548057566558413527)
          ·
            refine ⟨287273997822086349837620291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191515998548057566558413527 287273997822086349837620291)
            ·
              refine ⟨430910996733129524756430437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287273997822086349837620291 430910996733129524756430437)
              ·
                refine ⟨80795811887461785891830707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430910996733129524756430437 80795811887461785891830707)
                ·
                  refine ⟨121193717831192678837746061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80795811887461785891830707 121193717831192678837746061)
                  ·
                    refine ⟨45447644186697254564154773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121193717831192678837746061 45447644186697254564154773)
                    ·
                      refine ⟨2130358321251433807694755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45447644186697254564154773 2130358321251433807694755)
                      ·
                        rfl

theorem cell23_4148858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_4148858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148858 prefixEnd_4148858 := by exact prefixLift 4148858
  have htrace : WordTrace (prefixWord ++ tailWord_4148858) baseStart_4148858 baseEnd_4148858 := by
    simpa [prefixWord, tailWord_4148858, baseEnd_4148858] using wordTrace_append hprefix tailTrace_4148858
  have hstable : (prefixWord ++ tailWord_4148858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148858).length < 2 ^ (prefixWord ++ tailWord_4148858).sum := by decide
  have hdescent : baseEnd_4148858 < baseStart_4148858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148912 : List Nat := [2, 1, 1, 1, 2, 1, 4, 4, 3, 1, 3]
def baseStart_4148912 : Nat := 118140960795 + 4148912 * 2 ^ 59
def prefixEnd_4148912 : Nat := 4983230072969 + 3 ^ 40 * 4148912 * 2
def baseEnd_4148912 : Nat := 2130386049206776596419507

theorem tailTrace_4148912 : CollatzResearch.WordTrace tailWord_4148912 prefixEnd_4148912 2130386049206776596419507 := by
  unfold tailWord_4148912
  simp only [CollatzResearch.WordTrace]
  refine ⟨75661626172603938300976495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100882168230138584401301993 75661626172603938300976495)
  ·
    refine ⟨113492439258905907451464743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75661626172603938300976495 113492439258905907451464743)
    ·
      refine ⟨170238658888358861177197115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113492439258905907451464743 170238658888358861177197115)
      ·
        refine ⟨255357988332538291765795673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170238658888358861177197115 255357988332538291765795673)
        ·
          refine ⟨191518491249403718824346755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255357988332538291765795673 191518491249403718824346755)
          ·
            refine ⟨287277736874105578236520133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191518491249403718824346755 287277736874105578236520133)
            ·
              refine ⟨53864575663894795919347525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287277736874105578236520133 53864575663894795919347525)
              ·
                refine ⟨10099607936980274234877661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53864575663894795919347525 10099607936980274234877661)
                ·
                  refine ⟨3787352976367602838079123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10099607936980274234877661 3787352976367602838079123)
                  ·
                    refine ⟨5681029464551404257118685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787352976367602838079123 5681029464551404257118685)
                    ·
                      refine ⟨2130386049206776596419507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681029464551404257118685 2130386049206776596419507)
                      ·
                        rfl

theorem cell23_4148912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 3, 1, 3].length) (baseStart_4148912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148912 prefixEnd_4148912 := by exact prefixLift 4148912
  have htrace : WordTrace (prefixWord ++ tailWord_4148912) baseStart_4148912 baseEnd_4148912 := by
    simpa [prefixWord, tailWord_4148912, baseEnd_4148912] using wordTrace_append hprefix tailTrace_4148912
  have hstable : (prefixWord ++ tailWord_4148912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148912).length < 2 ^ (prefixWord ++ tailWord_4148912).sum := by decide
  have hdescent : baseEnd_4148912 < baseStart_4148912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148915 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 3, 5]
def baseStart_4148915 : Nat := 118140960795 + 4148915 * 2 ^ 59
def prefixEnd_4148915 : Nat := 4983230072969 + 3 ^ 40 * 4148915 * 2
def baseEnd_4148915 : Nat := 710129196549580028227331

theorem tailTrace_4148915 : CollatzResearch.WordTrace tailWord_4148915 prefixEnd_4148915 710129196549580028227331 := by
  unfold tailWord_4148915
  simp only [CollatzResearch.WordTrace]
  refine ⟨151323361764197008114312199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100882241176131338742874799 151323361764197008114312199)
  ·
    refine ⟨226985042646295512171468299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151323361764197008114312199 226985042646295512171468299)
    ·
      refine ⟨340477563969443268257202449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226985042646295512171468299 340477563969443268257202449)
      ·
        refine ⟨255358172977082451192901837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340477563969443268257202449 255358172977082451192901837)
        ·
          refine ⟨95759314866405919197338189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255358172977082451192901837 95759314866405919197338189)
          ·
            refine ⟨35909743074902219699001821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95759314866405919197338189 35909743074902219699001821)
            ·
              refine ⟨13466153653088332387125683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35909743074902219699001821 13466153653088332387125683)
              ·
                refine ⟨20199230479632498580688525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466153653088332387125683 20199230479632498580688525)
                ·
                  refine ⟨7574711429862186967758197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20199230479632498580688525 7574711429862186967758197)
                  ·
                    refine ⟨710129196549580028227331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7574711429862186967758197 710129196549580028227331)
                    ·
                      rfl

theorem cell23_4148915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 5].length) (baseStart_4148915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148915 prefixEnd_4148915 := by exact prefixLift 4148915
  have htrace : WordTrace (prefixWord ++ tailWord_4148915) baseStart_4148915 baseEnd_4148915 := by
    simpa [prefixWord, tailWord_4148915, baseEnd_4148915] using wordTrace_append hprefix tailTrace_4148915
  have hstable : (prefixWord ++ tailWord_4148915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148915).length < 2 ^ (prefixWord ++ tailWord_4148915).sum := by decide
  have hdescent : baseEnd_4148915 < baseStart_4148915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148940 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 1, 4]
def baseStart_4148940 : Nat := 118140960795 + 4148940 * 2 ^ 59
def prefixEnd_4148940 : Nat := 4983230072969 + 3 ^ 40 * 4148940 * 2
def baseEnd_4148940 : Nat := 710133475555034162289793

theorem tailTrace_4148940 : CollatzResearch.WordTrace tailWord_4148940 prefixEnd_4148940 710133475555034162289793 := by
  unfold tailWord_4148940
  simp only [CollatzResearch.WordTrace]
  refine ⟨75662136794553218691986137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100882849059404291589314849 75662136794553218691986137)
  ·
    refine ⟨56746602595914914018989603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75662136794553218691986137 56746602595914914018989603)
    ·
      refine ⟨85119903893872371028484405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56746602595914914018989603 85119903893872371028484405)
      ·
        refine ⟨7979990990050534783920413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85119903893872371028484405 7979990990050534783920413)
        ·
          refine ⟨2992496621268950543970155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7979990990050534783920413 2992496621268950543970155)
          ·
            refine ⟨4488744931903425815955233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992496621268950543970155 4488744931903425815955233)
            ·
              refine ⟨3366558698927569361966425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4488744931903425815955233 3366558698927569361966425)
              ·
                refine ⟨2524919024195677021474819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366558698927569361966425 2524919024195677021474819)
                ·
                  refine ⟨3787378536293515532212229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524919024195677021474819 3787378536293515532212229)
                  ·
                    refine ⟨710133475555034162289793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3787378536293515532212229 710133475555034162289793)
                    ·
                      rfl

theorem cell23_4148940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 4].length) (baseStart_4148940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148940 prefixEnd_4148940 := by exact prefixLift 4148940
  have htrace : WordTrace (prefixWord ++ tailWord_4148940) baseStart_4148940 baseEnd_4148940 := by
    simpa [prefixWord, tailWord_4148940, baseEnd_4148940] using wordTrace_append hprefix tailTrace_4148940
  have hstable : (prefixWord ++ tailWord_4148940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148940).length < 2 ^ (prefixWord ++ tailWord_4148940).sum := by decide
  have hdescent : baseEnd_4148940 < baseStart_4148940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148972 : List Nat := [2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 3]
def baseStart_4148972 : Nat := 118140960795 + 4148972 * 2 ^ 59
def prefixEnd_4148972 : Nat := 4983230072969 + 3 ^ 40 * 4148972 * 2
def baseEnd_4148972 : Nat := 2130416858046046361669231

theorem tailTrace_4148972 : CollatzResearch.WordTrace tailWord_4148972 prefixEnd_4148972 2130416858046046361669231 := by
  unfold tailWord_4148972
  simp only [CollatzResearch.WordTrace]
  refine ⟨75662720362495253424568585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100883627149993671232758113 75662720362495253424568585)
  ·
    refine ⟨56747040271871440068426439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75662720362495253424568585 56747040271871440068426439)
    ·
      refine ⟨85120560407807160102639659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56747040271871440068426439 85120560407807160102639659)
      ·
        refine ⟨127680840611710740153959489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85120560407807160102639659 127680840611710740153959489)
        ·
          refine ⟨95760630458783055115469617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127680840611710740153959489 95760630458783055115469617)
          ·
            refine ⟨71820472844087291336602213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95760630458783055115469617 71820472844087291336602213)
            ·
              refine ⟨13466338658266367125612915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71820472844087291336602213 13466338658266367125612915)
              ·
                refine ⟨20199507987399550688419373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466338658266367125612915 20199507987399550688419373)
                ·
                  refine ⟨7574815495274831508157265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20199507987399550688419373 7574815495274831508157265)
                  ·
                    refine ⟨5681111621456123631117949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7574815495274831508157265 5681111621456123631117949)
                    ·
                      refine ⟨2130416858046046361669231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681111621456123631117949 2130416858046046361669231)
                      ·
                        rfl

theorem cell23_4148972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 3].length) (baseStart_4148972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148972 prefixEnd_4148972 := by exact prefixLift 4148972
  have htrace : WordTrace (prefixWord ++ tailWord_4148972) baseStart_4148972 baseEnd_4148972 := by
    simpa [prefixWord, tailWord_4148972, baseEnd_4148972] using wordTrace_append hprefix tailTrace_4148972
  have hstable : (prefixWord ++ tailWord_4148972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148972).length < 2 ^ (prefixWord ++ tailWord_4148972).sum := by decide
  have hdescent : baseEnd_4148972 < baseStart_4148972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148980 : List Nat := [2, 6, 1, 1, 1, 1, 1, 5, 1, 1, 3]
def baseStart_4148980 : Nat := 118140960795 + 4148980 * 2 ^ 59
def prefixEnd_4148980 : Nat := 4983230072969 + 3 ^ 40 * 4148980 * 2
def baseEnd_4148980 : Nat := 2130420965891282330369195

theorem tailTrace_4148980 : CollatzResearch.WordTrace tailWord_4148980 prefixEnd_4148980 2130420965891282330369195 := by
  unfold tailWord_4148980
  simp only [CollatzResearch.WordTrace]
  refine ⟨75662866254480762107714197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100883821672641016143618929 75662866254480762107714197)
  ·
    refine ⟨3546696855678785723799103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75662866254480762107714197 3546696855678785723799103)
    ·
      refine ⟨5320045283518178585698655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546696855678785723799103 5320045283518178585698655)
      ·
        refine ⟨7980067925277267878547983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320045283518178585698655 7980067925277267878547983)
        ·
          refine ⟨11970101887915901817821975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7980067925277267878547983 11970101887915901817821975)
          ·
            refine ⟨17955152831873852726732963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970101887915901817821975 17955152831873852726732963)
            ·
              refine ⟨26932729247810779090099445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17955152831873852726732963 26932729247810779090099445)
              ·
                refine ⟨2524943366982260539696823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26932729247810779090099445 2524943366982260539696823)
                ·
                  refine ⟨3787415050473390809545235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2524943366982260539696823 3787415050473390809545235)
                  ·
                    refine ⟨5681122575710086214317853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787415050473390809545235 5681122575710086214317853)
                    ·
                      refine ⟨2130420965891282330369195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681122575710086214317853 2130420965891282330369195)
                      ·
                        rfl

theorem cell23_4148980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_4148980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148980 prefixEnd_4148980 := by exact prefixLift 4148980
  have htrace : WordTrace (prefixWord ++ tailWord_4148980) baseStart_4148980 baseEnd_4148980 := by
    simpa [prefixWord, tailWord_4148980, baseEnd_4148980] using wordTrace_append hprefix tailTrace_4148980
  have hstable : (prefixWord ++ tailWord_4148980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148980).length < 2 ^ (prefixWord ++ tailWord_4148980).sum := by decide
  have hdescent : baseEnd_4148980 < baseStart_4148980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4148996 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_4148996 : Nat := 118140960795 + 4148996 * 2 ^ 59
def prefixEnd_4148996 : Nat := 4983230072969 + 3 ^ 40 * 4148996 * 2
def baseEnd_4148996 : Nat := 710143060527251422589707

theorem tailTrace_4148996 : CollatzResearch.WordTrace tailWord_4148996 prefixEnd_4148996 710143060527251422589707 := by
  unfold tailWord_4148996
  simp only [CollatzResearch.WordTrace]
  refine ⟨75663158038451779474005421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100884210717935705965340561 75663158038451779474005421)
  ·
    refine ⟨28373684264419417302752033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75663158038451779474005421 28373684264419417302752033)
    ·
      refine ⟨21280263198314562977064025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28373684264419417302752033 21280263198314562977064025)
      ·
        refine ⟨15960197398735922232798019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21280263198314562977064025 15960197398735922232798019)
        ·
          refine ⟨23940296098103883349197029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960197398735922232798019 23940296098103883349197029)
          ·
            refine ⟨4488805518394478127974443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23940296098103883349197029 4488805518394478127974443)
            ·
              refine ⟨6733208277591717191961665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488805518394478127974443 6733208277591717191961665)
              ·
                refine ⟨5049906208193787893971249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6733208277591717191961665 5049906208193787893971249)
                ·
                  refine ⟨3787429656145340920478437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5049906208193787893971249 3787429656145340920478437)
                  ·
                    refine ⟨710143060527251422589707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3787429656145340920478437 710143060527251422589707)
                    ·
                      rfl

theorem cell23_4148996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_4148996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4148996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4148996 prefixEnd_4148996 := by exact prefixLift 4148996
  have htrace : WordTrace (prefixWord ++ tailWord_4148996) baseStart_4148996 baseEnd_4148996 := by
    simpa [prefixWord, tailWord_4148996, baseEnd_4148996] using wordTrace_append hprefix tailTrace_4148996
  have hstable : (prefixWord ++ tailWord_4148996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4148996).length < 2 ^ (prefixWord ++ tailWord_4148996).sum := by decide
  have hdescent : baseEnd_4148996 < baseStart_4148996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4148996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149032 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4149032 : Nat := 118140960795 + 4149032 * 2 ^ 59
def prefixEnd_4149032 : Nat := 4983230072969 + 3 ^ 40 * 4149032 * 2
def baseEnd_4149032 : Nat := 2130447666885316126918955

theorem tailTrace_4149032 : CollatzResearch.WordTrace tailWord_4149032 prefixEnd_4149032 2130447666885316126918955 := by
  unfold tailWord_4149032
  simp only [CollatzResearch.WordTrace]
  refine ⟨75663814552386568548160675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100885086069848758064214233 75663814552386568548160675)
  ·
    refine ⟨113495721828579852822241013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75663814552386568548160675 113495721828579852822241013)
    ·
      refine ⟨10640223921429361202085095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113495721828579852822241013 10640223921429361202085095)
      ·
        refine ⟨15960335882144041803127643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10640223921429361202085095 15960335882144041803127643)
        ·
          refine ⟨23940503823216062704691465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960335882144041803127643 23940503823216062704691465)
          ·
            refine ⟨17955377867412047028518599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23940503823216062704691465 17955377867412047028518599)
            ·
              refine ⟨26933066801118070542777899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17955377867412047028518599 26933066801118070542777899)
              ·
                refine ⟨40399600201677105814166849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26933066801118070542777899 40399600201677105814166849)
                ·
                  refine ⟨30299700151257829360625137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40399600201677105814166849 30299700151257829360625137)
                  ·
                    refine ⟨22724775113443372020468853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30299700151257829360625137 22724775113443372020468853)
                    ·
                      refine ⟨2130447666885316126918955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22724775113443372020468853 2130447666885316126918955)
                      ·
                        rfl

theorem cell23_4149032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4149032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149032 prefixEnd_4149032 := by exact prefixLift 4149032
  have htrace : WordTrace (prefixWord ++ tailWord_4149032) baseStart_4149032 baseEnd_4149032 := by
    simpa [prefixWord, tailWord_4149032, baseEnd_4149032] using wordTrace_append hprefix tailTrace_4149032
  have hstable : (prefixWord ++ tailWord_4149032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149032).length < 2 ^ (prefixWord ++ tailWord_4149032).sum := by decide
  have hdescent : baseEnd_4149032 < baseStart_4149032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149109 : List Nat := [1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 3]
def baseStart_4149109 : Nat := 118140960795 + 4149109 * 2 ^ 59
def prefixEnd_4149109 : Nat := 4983230072969 + 3 ^ 40 * 4149109 * 2
def baseEnd_4149109 : Nat := 2130487204895712325656101

theorem tailTrace_4149109 : CollatzResearch.WordTrace tailWord_4149109 prefixEnd_4149109 2130487204895712325656101 := by
  unfold tailWord_4149109
  simp only [CollatzResearch.WordTrace]
  refine ⟨151330437525494179246874381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100886958350329452831249587 151330437525494179246874381)
  ·
    refine ⟨56748914072060317217577893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151330437525494179246874381 56748914072060317217577893)
    ·
      refine ⟨10640421388511309478295855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56748914072060317217577893 10640421388511309478295855)
      ·
        refine ⟨15960632082766964217443783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10640421388511309478295855 15960632082766964217443783)
        ·
          refine ⟨23940948124150446326165675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15960632082766964217443783 23940948124150446326165675)
          ·
            refine ⟨35911422186225669489248513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23940948124150446326165675 35911422186225669489248513)
            ·
              refine ⟨26933566639669252116936385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35911422186225669489248513 26933566639669252116936385)
              ·
                refine ⟨20200174979751939087702289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26933566639669252116936385 20200174979751939087702289)
                ·
                  refine ⟨15150131234813954315776717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20200174979751939087702289 15150131234813954315776717)
                  ·
                    refine ⟨5681299213055232868416269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15150131234813954315776717 5681299213055232868416269)
                    ·
                      refine ⟨2130487204895712325656101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681299213055232868416269 2130487204895712325656101)
                      ·
                        rfl

theorem cell23_4149109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_4149109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149109 prefixEnd_4149109 := by exact prefixLift 4149109
  have htrace : WordTrace (prefixWord ++ tailWord_4149109) baseStart_4149109 baseEnd_4149109 := by
    simpa [prefixWord, tailWord_4149109, baseEnd_4149109] using wordTrace_append hprefix tailTrace_4149109
  have hstable : (prefixWord ++ tailWord_4149109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149109).length < 2 ^ (prefixWord ++ tailWord_4149109).sum := by decide
  have hdescent : baseEnd_4149109 < baseStart_4149109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149132 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 1, 3, 4]
def baseStart_4149132 : Nat := 118140960795 + 4149132 * 2 ^ 59
def prefixEnd_4149132 : Nat := 4983230072969 + 3 ^ 40 * 4149132 * 2
def baseEnd_4149132 : Nat := 2130499014950765735668495

theorem tailTrace_4149132 : CollatzResearch.WordTrace tailWord_4149132 prefixEnd_4149132 2130499014950765735668495 := by
  unfold tailWord_4149132
  simp only [CollatzResearch.WordTrace]
  refine ⟨75665638202205427087480825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100887517602940569449974433 75665638202205427087480825)
  ·
    refine ⟨56749228651654070315610619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75665638202205427087480825 56749228651654070315610619)
    ·
      refine ⟨85123842977481105473415929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56749228651654070315610619 85123842977481105473415929)
      ·
        refine ⟨63842882233110829105061947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85123842977481105473415929 63842882233110829105061947)
        ·
          refine ⟨95764323349666243657592921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63842882233110829105061947 95764323349666243657592921)
          ·
            refine ⟨71823242512249682743194691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95764323349666243657592921 71823242512249682743194691)
            ·
              refine ⟨107734863768374524114792037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71823242512249682743194691 107734863768374524114792037)
              ·
                refine ⟨20200286956570223271523507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107734863768374524114792037 20200286956570223271523507)
                ·
                  refine ⟨30300430434855334907285261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20200286956570223271523507 30300430434855334907285261)
                  ·
                    refine ⟨11362661413070750590231973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30300430434855334907285261 11362661413070750590231973)
                    ·
                      refine ⟨2130499014950765735668495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11362661413070750590231973 2130499014950765735668495)
                      ·
                        rfl

theorem cell23_4149132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_4149132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149132 prefixEnd_4149132 := by exact prefixLift 4149132
  have htrace : WordTrace (prefixWord ++ tailWord_4149132) baseStart_4149132 baseEnd_4149132 := by
    simpa [prefixWord, tailWord_4149132, baseEnd_4149132] using wordTrace_append hprefix tailTrace_4149132
  have hstable : (prefixWord ++ tailWord_4149132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149132).length < 2 ^ (prefixWord ++ tailWord_4149132).sum := by decide
  have hdescent : baseEnd_4149132 < baseStart_4149132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149146 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_4149146 : Nat := 118140960795 + 4149146 * 2 ^ 59
def prefixEnd_4149146 : Nat := 4983230072969 + 3 ^ 40 * 4149146 * 2
def baseEnd_4149146 : Nat := 710168734559976226964477

theorem tailTrace_4149146 : CollatzResearch.WordTrace tailWord_4149146 prefixEnd_4149146 710168734559976226964477 := by
  unfold tailWord_4149146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37832946756590033641492823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100887858017573423043980861 37832946756590033641492823)
  ·
    refine ⟨56749420134885050462239235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37832946756590033641492823 56749420134885050462239235)
    ·
      refine ⟨85124130202327575693358853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56749420134885050462239235 85124130202327575693358853)
      ·
        refine ⟨15960774412936420442504785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85124130202327575693358853 15960774412936420442504785)
        ·
          refine ⟨11970580809702315331878589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15960774412936420442504785 11970580809702315331878589)
          ·
            refine ⟨4488967803638368249454471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11970580809702315331878589 4488967803638368249454471)
            ·
              refine ⟨6733451705457552374181707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4488967803638368249454471 6733451705457552374181707)
              ·
                refine ⟨10100177558186328561272561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733451705457552374181707 10100177558186328561272561)
                ·
                  refine ⟨7575133168639746420954421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10100177558186328561272561 7575133168639746420954421)
                  ·
                    refine ⟨710168734559976226964477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7575133168639746420954421 710168734559976226964477)
                    ·
                      rfl

theorem cell23_4149146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_4149146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149146 prefixEnd_4149146 := by exact prefixLift 4149146
  have htrace : WordTrace (prefixWord ++ tailWord_4149146) baseStart_4149146 baseEnd_4149146 := by
    simpa [prefixWord, tailWord_4149146, baseEnd_4149146] using wordTrace_append hprefix tailTrace_4149146
  have hstable : (prefixWord ++ tailWord_4149146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149146).length < 2 ^ (prefixWord ++ tailWord_4149146).sum := by decide
  have hdescent : baseEnd_4149146 < baseStart_4149146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149149 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4149149 : Nat := 118140960795 + 4149149 * 2 ^ 59
def prefixEnd_4149149 : Nat := 4983230072969 + 3 ^ 40 * 4149149 * 2
def baseEnd_4149149 : Nat := 2130507744121892169155917

theorem tailTrace_4149149 : CollatzResearch.WordTrace tailWord_4149149 prefixEnd_4149149 2130507744121892169155917 := by
  unfold tailWord_4149149
  simp only [CollatzResearch.WordTrace]
  refine ⟨151331896445349266078330501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100887930963566177385553667 151331896445349266078330501)
  ·
    refine ⟨28374730583502987389686969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151331896445349266078330501 28374730583502987389686969)
    ·
      refine ⟨21281047937627240542265227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28374730583502987389686969 21281047937627240542265227)
      ·
        refine ⟨31921571906440860813397841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21281047937627240542265227 31921571906440860813397841)
        ·
          refine ⟨23941178929830645610048381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31921571906440860813397841 23941178929830645610048381)
          ·
            refine ⟨8977942098686492103768143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23941178929830645610048381 8977942098686492103768143)
            ·
              refine ⟨13466913148029738155652215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8977942098686492103768143 13466913148029738155652215)
              ·
                refine ⟨20200369722044607233478323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13466913148029738155652215 20200369722044607233478323)
                ·
                  refine ⟨30300554583066910850217485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20200369722044607233478323 30300554583066910850217485)
                  ·
                    refine ⟨11362707968650091568831557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30300554583066910850217485 11362707968650091568831557)
                    ·
                      refine ⟨2130507744121892169155917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11362707968650091568831557 2130507744121892169155917)
                      ·
                        rfl

theorem cell23_4149149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4149149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149149 prefixEnd_4149149 := by exact prefixLift 4149149
  have htrace : WordTrace (prefixWord ++ tailWord_4149149) baseStart_4149149 baseEnd_4149149 := by
    simpa [prefixWord, tailWord_4149149, baseEnd_4149149] using wordTrace_append hprefix tailTrace_4149149
  have hstable : (prefixWord ++ tailWord_4149149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149149).length < 2 ^ (prefixWord ++ tailWord_4149149).sum := by decide
  have hdescent : baseEnd_4149149 < baseStart_4149149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149150 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_4149150 : Nat := 118140960795 + 4149150 * 2 ^ 59
def prefixEnd_4149150 : Nat := 4983230072969 + 3 ^ 40 * 4149150 * 2
def baseEnd_4149150 : Nat := 236723139733616296138157

theorem tailTrace_4149150 : CollatzResearch.WordTrace tailWord_4149150 prefixEnd_4149150 236723139733616296138157 := by
  unfold tailWord_4149150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18916491614793205406139613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100887955278897095499411269 18916491614793205406139613)
  ·
    refine ⟨7093684355547452027302355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18916491614793205406139613 7093684355547452027302355)
    ·
      refine ⟨10640526533321178040953533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7093684355547452027302355 10640526533321178040953533)
      ·
        refine ⟨3990197449995441765357575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10640526533321178040953533 3990197449995441765357575)
        ·
          refine ⟨5985296174993162648036363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990197449995441765357575 5985296174993162648036363)
          ·
            refine ⟨8977944262489743972054545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5985296174993162648036363 8977944262489743972054545)
            ·
              refine ⟨6733458196867307979040909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8977944262489743972054545 6733458196867307979040909)
              ·
                refine ⟨2525046823825240492140341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6733458196867307979040909 2525046823825240492140341)
                ·
                  refine ⟨236723139733616296138157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2525046823825240492140341 236723139733616296138157)
                  ·
                    rfl

theorem cell23_4149150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_4149150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149150 prefixEnd_4149150 := by exact prefixLift 4149150
  have htrace : WordTrace (prefixWord ++ tailWord_4149150) baseStart_4149150 baseEnd_4149150 := by
    simpa [prefixWord, tailWord_4149150, baseEnd_4149150] using wordTrace_append hprefix tailTrace_4149150
  have hstable : (prefixWord ++ tailWord_4149150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149150).length < 2 ^ (prefixWord ++ tailWord_4149150).sum := by decide
  have hdescent : baseEnd_4149150 < baseStart_4149150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149176 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 1, 4]
def baseStart_4149176 : Nat := 118140960795 + 4149176 * 2 ^ 59
def prefixEnd_4149176 : Nat := 4983230072969 + 3 ^ 40 * 4149176 * 2
def baseEnd_4149176 : Nat := 710173869366521187839431

theorem tailTrace_4149176 : CollatzResearch.WordTrace tailWord_4149176 prefixEnd_4149176 710173869366521187839431 := by
  unfold tailWord_4149176
  simp only [CollatzResearch.WordTrace]
  refine ⟨75666440608125724844781691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100888587477500966459708921 75666440608125724844781691)
  ·
    refine ⟨113499660912188587267172537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75666440608125724844781691 113499660912188587267172537)
    ·
      refine ⟨85124745684141440450379403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113499660912188587267172537 85124745684141440450379403)
      ·
        refine ⟨127687118526212160675569105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85124745684141440450379403 127687118526212160675569105)
        ·
          refine ⟨95765338894659120506676829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127687118526212160675569105 95765338894659120506676829)
          ·
            refine ⟨35912002085497170190003811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95765338894659120506676829 35912002085497170190003811)
            ·
              refine ⟨53868003128245755285005717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35912002085497170190003811 53868003128245755285005717)
              ·
                refine ⟨2525062646636519778984643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53868003128245755285005717 2525062646636519778984643)
                ·
                  refine ⟨3787593969954779668476965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525062646636519778984643 3787593969954779668476965)
                  ·
                    refine ⟨710173869366521187839431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3787593969954779668476965 710173869366521187839431)
                    ·
                      rfl

theorem cell23_4149176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 4].length) (baseStart_4149176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149176 prefixEnd_4149176 := by exact prefixLift 4149176
  have htrace : WordTrace (prefixWord ++ tailWord_4149176) baseStart_4149176 baseEnd_4149176 := by
    simpa [prefixWord, tailWord_4149176, baseEnd_4149176] using wordTrace_append hprefix tailTrace_4149176
  have hstable : (prefixWord ++ tailWord_4149176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149176).length < 2 ^ (prefixWord ++ tailWord_4149176).sum := by decide
  have hdescent : baseEnd_4149176 < baseStart_4149176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149210 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_4149210 : Nat := 118140960795 + 4149210 * 2 ^ 59
def prefixEnd_4149210 : Nat := 4983230072969 + 3 ^ 40 * 4149210 * 2
def baseEnd_4149210 : Nat := 710179688813938810164379

theorem tailTrace_4149210 : CollatzResearch.WordTrace tailWord_4149210 prefixEnd_4149210 710179688813938810164379 := by
  unfold tailWord_4149210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37833530324532068374075271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100889414198752182330867389 37833530324532068374075271)
  ·
    refine ⟨56750295486798102561112907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37833530324532068374075271 56750295486798102561112907)
    ·
      refine ⟨85125443230197153841669361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56750295486798102561112907 85125443230197153841669361)
      ·
        refine ⟨63844082422647865381252021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85125443230197153841669361 63844082422647865381252021)
        ·
          refine ⟨5985382727123237379492377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63844082422647865381252021 5985382727123237379492377)
          ·
            refine ⟨4489037045342428034619283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5985382727123237379492377 4489037045342428034619283)
            ·
              refine ⟨6733555568013642051928925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489037045342428034619283 6733555568013642051928925)
              ·
                refine ⟨2525083338005115769473347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6733555568013642051928925 2525083338005115769473347)
                ·
                  refine ⟨3787625007007673654210021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525083338005115769473347 3787625007007673654210021)
                  ·
                    refine ⟨710179688813938810164379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3787625007007673654210021 710179688813938810164379)
                    ·
                      rfl

theorem cell23_4149210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_4149210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149210 prefixEnd_4149210 := by exact prefixLift 4149210
  have htrace : WordTrace (prefixWord ++ tailWord_4149210) baseStart_4149210 baseEnd_4149210 := by
    simpa [prefixWord, tailWord_4149210, baseEnd_4149210] using wordTrace_append hprefix tailTrace_4149210
  have hstable : (prefixWord ++ tailWord_4149210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149210).length < 2 ^ (prefixWord ++ tailWord_4149210).sum := by decide
  have hdescent : baseEnd_4149210 < baseStart_4149210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149249 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 1, 6]
def baseStart_4149249 : Nat := 118140960795 + 4149249 * 2 ^ 59
def prefixEnd_4149249 : Nat := 4983230072969 + 3 ^ 40 * 4149249 * 2
def baseEnd_4149249 : Nat := 710186364062447259301819

theorem tailTrace_4149249 : CollatzResearch.WordTrace tailWord_4149249 prefixEnd_4149249 710186364062447259301819 := by
  unfold tailWord_4149249
  simp only [CollatzResearch.WordTrace]
  refine ⟨151335543744986983156970801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100890362496657988771313867 151335543744986983156970801)
  ·
    refine ⟨113501657808740237367728101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151335543744986983156970801 113501657808740237367728101)
    ·
      refine ⟨21281560839138794506449019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113501657808740237367728101 21281560839138794506449019)
      ·
        refine ⟨31922341258708191759673529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21281560839138794506449019 31922341258708191759673529)
        ·
          refine ⟨23941755944031143819755147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31922341258708191759673529 23941755944031143819755147)
          ·
            refine ⟨35912633916046715729632721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23941755944031143819755147 35912633916046715729632721)
            ·
              refine ⟨26934475437035036797224541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35912633916046715729632721 26934475437035036797224541)
              ·
                refine ⟨10100428288888138798959203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26934475437035036797224541 10100428288888138798959203)
                ·
                  refine ⟨15150642433332208198438805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100428288888138798959203 15150642433332208198438805)
                  ·
                    refine ⟨710186364062447259301819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15150642433332208198438805 710186364062447259301819)
                    ·
                      rfl

theorem cell23_4149249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_4149249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149249 prefixEnd_4149249 := by exact prefixLift 4149249
  have htrace : WordTrace (prefixWord ++ tailWord_4149249) baseStart_4149249 baseEnd_4149249 := by
    simpa [prefixWord, tailWord_4149249, baseEnd_4149249] using wordTrace_append hprefix tailTrace_4149249
  have hstable : (prefixWord ++ tailWord_4149249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149249).length < 2 ^ (prefixWord ++ tailWord_4149249).sum := by decide
  have hdescent : baseEnd_4149249 < baseStart_4149249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149254 : List Nat := [6, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4149254 : Nat := 118140960795 + 4149254 * 2 ^ 59
def prefixEnd_4149254 : Nat := 4983230072969 + 3 ^ 40 * 4149254 * 2
def baseEnd_4149254 : Nat := 2130561659590614258342935

theorem tailTrace_4149254 : CollatzResearch.WordTrace tailWord_4149254 prefixEnd_4149254 2130561659590614258342935 := by
  unfold tailWord_4149254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4729241440936527156590713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100890484073312579340601877 4729241440936527156590713)
  ·
    refine ⟨3546931080702395367443035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4729241440936527156590713 3546931080702395367443035)
    ·
      refine ⟨5320396621053593051164553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3546931080702395367443035 5320396621053593051164553)
      ·
        refine ⟨3990297465790194788373415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5320396621053593051164553 3990297465790194788373415)
        ·
          refine ⟨5985446198685292182560123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990297465790194788373415 5985446198685292182560123)
          ·
            refine ⟨8978169298027938273840185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5985446198685292182560123 8978169298027938273840185)
            ·
              refine ⟨6733626973520953705380139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8978169298027938273840185 6733626973520953705380139)
              ·
                refine ⟨10100440460281430558070209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733626973520953705380139 10100440460281430558070209)
                ·
                  refine ⟨7575330345211072918552657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10100440460281430558070209 7575330345211072918552657)
                  ·
                    refine ⟨5681497758908304688914493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575330345211072918552657 5681497758908304688914493)
                    ·
                      refine ⟨2130561659590614258342935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681497758908304688914493 2130561659590614258342935)
                      ·
                        rfl

theorem cell23_4149254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4149254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149254 prefixEnd_4149254 := by exact prefixLift 4149254
  have htrace : WordTrace (prefixWord ++ tailWord_4149254) baseStart_4149254 baseEnd_4149254 := by
    simpa [prefixWord, tailWord_4149254, baseEnd_4149254] using wordTrace_append hprefix tailTrace_4149254
  have hstable : (prefixWord ++ tailWord_4149254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149254).length < 2 ^ (prefixWord ++ tailWord_4149254).sum := by decide
  have hdescent : baseEnd_4149254 < baseStart_4149254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149276 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 1, 1, 5]
def baseStart_4149276 : Nat := 118140960795 + 4149276 * 2 ^ 59
def prefixEnd_4149276 : Nat := 4983230072969 + 3 ^ 40 * 4149276 * 2
def baseEnd_4149276 : Nat := 2130572956165013172267833

theorem tailTrace_4149276 : CollatzResearch.WordTrace tailWord_4149276 prefixEnd_4149276 2130572956165013172267833 := by
  unfold tailWord_4149276
  simp only [CollatzResearch.WordTrace]
  refine ⟨75668264257944583384101841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100891019010592777845469121 75668264257944583384101841)
  ·
    refine ⟨56751198193458437538076381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75668264257944583384101841 56751198193458437538076381)
    ·
      refine ⟨21281699322546914076778643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56751198193458437538076381 21281699322546914076778643)
      ·
        refine ⟨31922548983820371115167965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21281699322546914076778643 31922548983820371115167965)
        ·
          refine ⟨11970955868932639168187987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31922548983820371115167965 11970955868932639168187987)
          ·
            refine ⟨17956433803398958752281981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11970955868932639168187987 17956433803398958752281981)
            ·
              refine ⟨6733662676274609532105743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17956433803398958752281981 6733662676274609532105743)
              ·
                refine ⟨10100494014411914298158615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6733662676274609532105743 10100494014411914298158615)
                ·
                  refine ⟨15150741021617871447237923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10100494014411914298158615 15150741021617871447237923)
                  ·
                    refine ⟨22726111532426807170856885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15150741021617871447237923 22726111532426807170856885)
                    ·
                      refine ⟨2130572956165013172267833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22726111532426807170856885 2130572956165013172267833)
                      ·
                        rfl

theorem cell23_4149276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_4149276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149276 prefixEnd_4149276 := by exact prefixLift 4149276
  have htrace : WordTrace (prefixWord ++ tailWord_4149276) baseStart_4149276 baseEnd_4149276 := by
    simpa [prefixWord, tailWord_4149276, baseEnd_4149276] using wordTrace_append hprefix tailTrace_4149276
  have hstable : (prefixWord ++ tailWord_4149276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149276).length < 2 ^ (prefixWord ++ tailWord_4149276).sum := by decide
  have hdescent : baseEnd_4149276 < baseStart_4149276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149284 : List Nat := [2, 3, 1, 4, 2, 2, 2, 2, 1, 1, 3]
def baseStart_4149284 : Nat := 118140960795 + 4149284 * 2 ^ 59
def prefixEnd_4149284 : Nat := 4983230072969 + 3 ^ 40 * 4149284 * 2
def baseEnd_4149284 : Nat := 2130577064010249140967797

theorem tailTrace_4149284 : CollatzResearch.WordTrace tailWord_4149284 prefixEnd_4149284 2130577064010249140967797 := by
  unfold tailWord_4149284
  simp only [CollatzResearch.WordTrace]
  refine ⟨75668410149930092067247453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100891213533240122756329937 75668410149930092067247453)
  ·
    refine ⟨28375653806223784525217795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75668410149930092067247453 28375653806223784525217795)
    ·
      refine ⟨42563480709335676787826693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28375653806223784525217795 42563480709335676787826693)
      ·
        refine ⟨7980652633000439397717505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42563480709335676787826693 7980652633000439397717505)
        ·
          refine ⟨5985489474750329548288129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7980652633000439397717505 5985489474750329548288129)
          ·
            refine ⟨4489117106062747161216097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5985489474750329548288129 4489117106062747161216097)
            ·
              refine ⟨3366837829547060370912073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489117106062747161216097 3366837829547060370912073)
              ·
                refine ⟨2525128372160295278184055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366837829547060370912073 2525128372160295278184055)
                ·
                  refine ⟨3787692558240442917276083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525128372160295278184055 3787692558240442917276083)
                  ·
                    refine ⟨5681538837360664375914125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787692558240442917276083 5681538837360664375914125)
                    ·
                      refine ⟨2130577064010249140967797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681538837360664375914125 2130577064010249140967797)
                      ·
                        rfl

theorem cell23_4149284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_4149284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149284 prefixEnd_4149284 := by exact prefixLift 4149284
  have htrace : WordTrace (prefixWord ++ tailWord_4149284) baseStart_4149284 baseEnd_4149284 := by
    simpa [prefixWord, tailWord_4149284, baseEnd_4149284] using wordTrace_append hprefix tailTrace_4149284
  have hstable : (prefixWord ++ tailWord_4149284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149284).length < 2 ^ (prefixWord ++ tailWord_4149284).sum := by decide
  have hdescent : baseEnd_4149284 < baseStart_4149284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149306 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3]
def baseStart_4149306 : Nat := 118140960795 + 4149306 * 2 ^ 59
def prefixEnd_4149306 : Nat := 4983230072969 + 3 ^ 40 * 4149306 * 2
def baseEnd_4149306 : Nat := 2130588360584648054892695

theorem tailTrace_4149306 : CollatzResearch.WordTrace tailWord_4149306 prefixEnd_4149306 2130588360584648054892695 := by
  unfold tailWord_4149306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37834405676445120472948943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100891748470520321261197181 37834405676445120472948943)
  ·
    refine ⟨56751608514667680709423415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37834405676445120472948943 56751608514667680709423415)
    ·
      refine ⟨85127412772001521064135123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56751608514667680709423415 85127412772001521064135123)
      ·
        refine ⟨127691119158002281596202685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85127412772001521064135123 127691119158002281596202685)
        ·
          refine ⟨47884169684250855598576007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127691119158002281596202685 47884169684250855598576007)
          ·
            refine ⟨71826254526376283397864011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47884169684250855598576007 71826254526376283397864011)
            ·
              refine ⟨107739381789564425096796017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71826254526376283397864011 107739381789564425096796017)
              ·
                refine ⟨80804536342173318822597013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107739381789564425096796017 80804536342173318822597013)
                ·
                  refine ⟨3787712641039374319809235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 80804536342173318822597013 3787712641039374319809235)
                  ·
                    refine ⟨5681568961559061479713853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787712641039374319809235 5681568961559061479713853)
                    ·
                      refine ⟨2130588360584648054892695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681568961559061479713853 2130588360584648054892695)
                      ·
                        rfl

theorem cell23_4149306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3].length) (baseStart_4149306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149306 prefixEnd_4149306 := by exact prefixLift 4149306
  have htrace : WordTrace (prefixWord ++ tailWord_4149306) baseStart_4149306 baseEnd_4149306 := by
    simpa [prefixWord, tailWord_4149306, baseEnd_4149306] using wordTrace_append hprefix tailTrace_4149306
  have hstable : (prefixWord ++ tailWord_4149306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149306).length < 2 ^ (prefixWord ++ tailWord_4149306).sum := by decide
  have hdescent : baseEnd_4149306 < baseStart_4149306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149309 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_4149309 : Nat := 118140960795 + 4149309 * 2 ^ 59
def prefixEnd_4149309 : Nat := 4983230072969 + 3 ^ 40 * 4149309 * 2
def baseEnd_4149309 : Nat := 710196633675537181051727

theorem tailTrace_4149309 : CollatzResearch.WordTrace tailWord_4149309 prefixEnd_4149309 710196633675537181051727 := by
  unfold tailWord_4149309
  simp only [CollatzResearch.WordTrace]
  refine ⟨151337732124769613404154981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100891821416513075602769987 151337732124769613404154981)
  ·
    refine ⟨28375824773394302513279059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151337732124769613404154981 28375824773394302513279059)
    ·
      refine ⟨42563737160091453769918589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28375824773394302513279059 42563737160091453769918589)
      ·
        refine ⟨15961401435034295163719471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42563737160091453769918589 15961401435034295163719471)
        ·
          refine ⟨23942102152551442745579207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15961401435034295163719471 23942102152551442745579207)
          ·
            refine ⟨35913153228827164118368811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23942102152551442745579207 35913153228827164118368811)
            ·
              refine ⟨53869729843240746177553217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35913153228827164118368811 53869729843240746177553217)
              ·
                refine ⟨40402297382430559633164913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53869729843240746177553217 40402297382430559633164913)
                ·
                  refine ⟨30301723036822919724873685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40402297382430559633164913 30301723036822919724873685)
                  ·
                    refine ⟨710196633675537181051727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30301723036822919724873685 710196633675537181051727)
                    ·
                      rfl

theorem cell23_4149309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_4149309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149309 prefixEnd_4149309 := by exact prefixLift 4149309
  have htrace : WordTrace (prefixWord ++ tailWord_4149309) baseStart_4149309 baseEnd_4149309 := by
    simpa [prefixWord, tailWord_4149309, baseEnd_4149309] using wordTrace_append hprefix tailTrace_4149309
  have hstable : (prefixWord ++ tailWord_4149309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149309).length < 2 ^ (prefixWord ++ tailWord_4149309).sum := by decide
  have hdescent : baseEnd_4149309 < baseStart_4149309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149319 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_4149319 : Nat := 118140960795 + 4149319 * 2 ^ 59
def prefixEnd_4149319 : Nat := 4983230072969 + 3 ^ 40 * 4149319 * 2
def baseEnd_4149319 : Nat := 2130595035833156504030135

theorem tailTrace_4149319 : CollatzResearch.WordTrace tailWord_4149319 prefixEnd_4149319 2130595035833156504030135 := by
  unfold tailWord_4149319
  simp only [CollatzResearch.WordTrace]
  refine ⟨151338096854733385112019011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100892064569822256741346007 151338096854733385112019011)
  ·
    refine ⟨227007145282100077668028517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151338096854733385112019011 227007145282100077668028517)
    ·
      refine ⟨42563839740393764562755347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227007145282100077668028517 42563839740393764562755347)
      ·
        refine ⟨63845759610590646844133021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42563839740393764562755347 63845759610590646844133021)
        ·
          refine ⟨23942159853971492566549883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63845759610590646844133021 23942159853971492566549883)
          ·
            refine ⟨35913239780957238849824825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23942159853971492566549883 35913239780957238849824825)
            ·
              refine ⟨26934929835717929137368619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35913239780957238849824825 26934929835717929137368619)
              ·
                refine ⟨40402394753576893706052929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26934929835717929137368619 40402394753576893706052929)
                ·
                  refine ⟨30301796065182670279539697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40402394753576893706052929 30301796065182670279539697)
                  ·
                    refine ⟨22726347048887002709654773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30301796065182670279539697 22726347048887002709654773)
                    ·
                      refine ⟨2130595035833156504030135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22726347048887002709654773 2130595035833156504030135)
                      ·
                        rfl

theorem cell23_4149319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_4149319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149319 prefixEnd_4149319 := by exact prefixLift 4149319
  have htrace : WordTrace (prefixWord ++ tailWord_4149319) baseStart_4149319 baseEnd_4149319 := by
    simpa [prefixWord, tailWord_4149319, baseEnd_4149319] using wordTrace_append hprefix tailTrace_4149319
  have hstable : (prefixWord ++ tailWord_4149319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149319).length < 2 ^ (prefixWord ++ tailWord_4149319).sum := by decide
  have hdescent : baseEnd_4149319 < baseStart_4149319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149340 : List Nat := [2, 2, 4, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_4149340 : Nat := 118140960795 + 4149340 * 2 ^ 59
def prefixEnd_4149340 : Nat := 4983230072969 + 3 ^ 40 * 4149340 * 2
def baseEnd_4149340 : Nat := 2130605818926900921867539

theorem tailTrace_4149340 : CollatzResearch.WordTrace tailWord_4149340 prefixEnd_4149340 2130605818926900921867539 := by
  unfold tailWord_4149340
  simp only [CollatzResearch.WordTrace]
  refine ⟨75669431393828652849266737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100892575191771537132355649 75669431393828652849266737)
  ·
    refine ⟨56752073545371489636950053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75669431393828652849266737 56752073545371489636950053)
    ·
      refine ⟨10641013789757154306928135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56752073545371489636950053 10641013789757154306928135)
      ·
        refine ⟨15961520684635731460392203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10641013789757154306928135 15961520684635731460392203)
        ·
          refine ⟨23942281026953597190588305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15961520684635731460392203 23942281026953597190588305)
          ·
            refine ⟨17956710770215197892941229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23942281026953597190588305 17956710770215197892941229)
            ·
              refine ⟨6733766538830699209852961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17956710770215197892941229 6733766538830699209852961)
              ·
                refine ⟨5050324904123024407389721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6733766538830699209852961 5050324904123024407389721)
                ·
                  refine ⟨3787743678092268305542291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5050324904123024407389721 3787743678092268305542291)
                  ·
                    refine ⟨5681615517138402458313437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787743678092268305542291 5681615517138402458313437)
                    ·
                      refine ⟨2130605818926900921867539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681615517138402458313437 2130605818926900921867539)
                      ·
                        rfl

theorem cell23_4149340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_4149340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149340 prefixEnd_4149340 := by exact prefixLift 4149340
  have htrace : WordTrace (prefixWord ++ tailWord_4149340) baseStart_4149340 baseEnd_4149340 := by
    simpa [prefixWord, tailWord_4149340, baseEnd_4149340] using wordTrace_append hprefix tailTrace_4149340
  have hstable : (prefixWord ++ tailWord_4149340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149340).length < 2 ^ (prefixWord ++ tailWord_4149340).sum := by decide
  have hdescent : baseEnd_4149340 < baseStart_4149340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149490 : List Nat := [3, 2, 1, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_4149490 : Nat := 118140960795 + 4149490 * 2 ^ 59
def prefixEnd_4149490 : Nat := 4983230072969 + 3 ^ 40 * 4149490 * 2
def baseEnd_4149490 : Nat := 2130682841025075334991849

theorem tailTrace_4149490 : CollatzResearch.WordTrace tailWord_4149490 prefixEnd_4149490 2130682841025075334991849 := by
  unfold tailWord_4149490
  simp only [CollatzResearch.WordTrace]
  refine ⟨37836083434278470329123481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100896222491409254210995949 37836083434278470329123481)
  ·
    refine ⟨28377062575708852746842611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37836083434278470329123481 28377062575708852746842611)
    ·
      refine ⟨42565593863563279120263917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28377062575708852746842611 42565593863563279120263917)
      ·
        refine ⟨15962097698836229670098969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42565593863563279120263917 15962097698836229670098969)
        ·
          refine ⟨11971573274127172252574227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15962097698836229670098969 11971573274127172252574227)
          ·
            refine ⟨17957359911190758378861341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11971573274127172252574227 17957359911190758378861341)
            ·
              refine ⟨6734009966696534392073003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17957359911190758378861341 6734009966696534392073003)
              ·
                refine ⟨10101014950044801588109505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734009966696534392073003 10101014950044801588109505)
                ·
                  refine ⟨7575761212533601191082129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10101014950044801588109505 7575761212533601191082129)
                  ·
                    refine ⟨5681820909400200893311597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7575761212533601191082129 5681820909400200893311597)
                    ·
                      refine ⟨2130682841025075334991849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681820909400200893311597 2130682841025075334991849)
                      ·
                        rfl

theorem cell23_4149490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_4149490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149490 prefixEnd_4149490 := by exact prefixLift 4149490
  have htrace : WordTrace (prefixWord ++ tailWord_4149490) baseStart_4149490 baseEnd_4149490 := by
    simpa [prefixWord, tailWord_4149490, baseEnd_4149490] using wordTrace_append hprefix tailTrace_4149490
  have hstable : (prefixWord ++ tailWord_4149490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149490).length < 2 ^ (prefixWord ++ tailWord_4149490).sum := by decide
  have hdescent : baseEnd_4149490 < baseStart_4149490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149503 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 3]
def baseStart_4149503 : Nat := 118140960795 + 4149503 * 2 ^ 59
def prefixEnd_4149503 : Nat := 4983230072969 + 3 ^ 40 * 4149503 * 2
def baseEnd_4149503 : Nat := 2130689516273583784129289

theorem tailTrace_4149503 : CollatzResearch.WordTrace tailWord_4149503 prefixEnd_4149503 2130689516273583784129289 := by
  unfold tailWord_4149503
  simp only [CollatzResearch.WordTrace]
  refine ⟨151344807886066784536717163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100896538590711189691144775 151344807886066784536717163)
  ·
    refine ⟨227017211829100176805075745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151344807886066784536717163 227017211829100176805075745)
    ·
      refine ⟨170262908871825132603806809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227017211829100176805075745 170262908871825132603806809)
      ·
        refine ⟨127697181653868849452855107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170262908871825132603806809 127697181653868849452855107)
        ·
          refine ⟨191545772480803274179282661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127697181653868849452855107 191545772480803274179282661)
          ·
            refine ⟨35914832340150613908615499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191545772480803274179282661 35914832340150613908615499)
            ·
              refine ⟨53872248510225920862923249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35914832340150613908615499 53872248510225920862923249)
              ·
                refine ⟨40404186382669440647192437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53872248510225920862923249 40404186382669440647192437)
                ·
                  refine ⟨3787892473375260060674291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40404186382669440647192437 3787892473375260060674291)
                  ·
                    refine ⟨5681838710062890091011437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3787892473375260060674291 5681838710062890091011437)
                    ·
                      refine ⟨2130689516273583784129289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681838710062890091011437 2130689516273583784129289)
                      ·
                        rfl

theorem cell23_4149503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_4149503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149503 prefixEnd_4149503 := by exact prefixLift 4149503
  have htrace : WordTrace (prefixWord ++ tailWord_4149503) baseStart_4149503 baseEnd_4149503 := by
    simpa [prefixWord, tailWord_4149503, baseEnd_4149503] using wordTrace_append hprefix tailTrace_4149503
  have hstable : (prefixWord ++ tailWord_4149503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149503).length < 2 ^ (prefixWord ++ tailWord_4149503).sum := by decide
  have hdescent : baseEnd_4149503 < baseStart_4149503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149540 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 1, 5]
def baseStart_4149540 : Nat := 118140960795 + 4149540 * 2 ^ 59
def prefixEnd_4149540 : Nat := 4983230072969 + 3 ^ 40 * 4149540 * 2
def baseEnd_4149540 : Nat := 710236171685933379788873

theorem tailTrace_4149540 : CollatzResearch.WordTrace tailWord_4149540 prefixEnd_4149540 710236171685933379788873 := by
  unfold tailWord_4149540
  simp only [CollatzResearch.WordTrace]
  refine ⟨75673078693466369927907037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100897438257955159903876049 75673078693466369927907037)
  ·
    refine ⟨28377404510049888722965139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75673078693466369927907037 28377404510049888722965139)
    ·
      refine ⟨42566106765074833084447709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28377404510049888722965139 42566106765074833084447709)
      ·
        refine ⟨15962290036903062406667891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42566106765074833084447709 15962290036903062406667891)
        ·
          refine ⟨23943435055354593610001837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962290036903062406667891 23943435055354593610001837)
          ·
            refine ⟨8978788145757972603750689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23943435055354593610001837 8978788145757972603750689)
            ·
              refine ⟨6734091109318479452813017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8978788145757972603750689 6734091109318479452813017)
              ·
                refine ⟨5050568331988859589609763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734091109318479452813017 5050568331988859589609763)
                ·
                  refine ⟨7575852497983289384414645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050568331988859589609763 7575852497983289384414645)
                  ·
                    refine ⟨710236171685933379788873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7575852497983289384414645 710236171685933379788873)
                    ·
                      rfl

theorem cell23_4149540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 5].length) (baseStart_4149540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149540 prefixEnd_4149540 := by exact prefixLift 4149540
  have htrace : WordTrace (prefixWord ++ tailWord_4149540) baseStart_4149540 baseEnd_4149540 := by
    simpa [prefixWord, tailWord_4149540, baseEnd_4149540] using wordTrace_append hprefix tailTrace_4149540
  have hstable : (prefixWord ++ tailWord_4149540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149540).length < 2 ^ (prefixWord ++ tailWord_4149540).sum := by decide
  have hdescent : baseEnd_4149540 < baseStart_4149540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149560 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 5, 2, 2]
def baseStart_4149560 : Nat := 118140960795 + 4149560 * 2 ^ 59
def prefixEnd_4149560 : Nat := 4983230072969 + 3 ^ 40 * 4149560 * 2
def baseEnd_4149560 : Nat := 2130718784670890061116527

theorem tailTrace_4149560 : CollatzResearch.WordTrace tailWord_4149560 prefixEnd_4149560 2130718784670890061116527 := by
  unfold tailWord_4149560
  simp only [CollatzResearch.WordTrace]
  refine ⟨75673443423430141635771067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100897924564573522181028089 75673443423430141635771067)
  ·
    refine ⟨113510165135145212453656601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75673443423430141635771067 113510165135145212453656601)
    ·
      refine ⟨85132623851358909340242451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113510165135145212453656601 85132623851358909340242451)
      ·
        refine ⟨127698935777038364010363677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85132623851358909340242451 127698935777038364010363677)
        ·
          refine ⟨47887100916389386503886379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127698935777038364010363677 47887100916389386503886379)
          ·
            refine ⟨71830651374584079755829569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47887100916389386503886379 71830651374584079755829569)
            ·
              refine ⟨53872988530938059816872177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71830651374584079755829569 53872988530938059816872177)
              ·
                refine ⟨40404741398203544862654133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53872988530938059816872177 40404741398203544862654133)
                ·
                  refine ⟨3787944506081582330873825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40404741398203544862654133 3787944506081582330873825)
                  ·
                    refine ⟨2840958379561186748155369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3787944506081582330873825 2840958379561186748155369)
                    ·
                      refine ⟨2130718784670890061116527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2840958379561186748155369 2130718784670890061116527)
                      ·
                        rfl

theorem cell23_4149560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 5, 2, 2].length) (baseStart_4149560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149560 prefixEnd_4149560 := by exact prefixLift 4149560
  have htrace : WordTrace (prefixWord ++ tailWord_4149560) baseStart_4149560 baseEnd_4149560 := by
    simpa [prefixWord, tailWord_4149560, baseEnd_4149560] using wordTrace_append hprefix tailTrace_4149560
  have hstable : (prefixWord ++ tailWord_4149560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149560).length < 2 ^ (prefixWord ++ tailWord_4149560).sum := by decide
  have hdescent : baseEnd_4149560 < baseStart_4149560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149593 : List Nat := [1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_4149593 : Nat := 118140960795 + 4149593 * 2 ^ 59
def prefixEnd_4149593 : Nat := 4983230072969 + 3 ^ 40 * 4149593 * 2
def baseEnd_4149593 : Nat := 2130735729532488432003875

theorem tailTrace_4149593 : CollatzResearch.WordTrace tailWord_4149593 prefixEnd_4149593 2130735729532488432003875 := by
  unfold tailWord_4149593
  simp only [CollatzResearch.WordTrace]
  refine ⟨151348090455740729907493433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100898726970493819938328955 151348090455740729907493433)
  ·
    refine ⟨113511067841805547430620075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151348090455740729907493433 113511067841805547430620075)
    ·
      refine ⟨170266601762708321145930113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113511067841805547430620075 170266601762708321145930113)
      ·
        refine ⟨127699951322031240859447585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170266601762708321145930113 127699951322031240859447585)
        ·
          refine ⟨95774963491523430644585689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127699951322031240859447585 95774963491523430644585689)
          ·
            refine ⟨71831222618642572983439267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95774963491523430644585689 71831222618642572983439267)
            ·
              refine ⟨107746833927963859475158901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71831222618642572983439267 107746833927963859475158901)
              ·
                refine ⟨10101265680746611825796147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107746833927963859475158901 10101265680746611825796147)
                ·
                  refine ⟨15151898521119917738694221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10101265680746611825796147 15151898521119917738694221)
                  ·
                    refine ⟨5681961945419969152010333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15151898521119917738694221 5681961945419969152010333)
                    ·
                      refine ⟨2130735729532488432003875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681961945419969152010333 2130735729532488432003875)
                      ·
                        rfl

theorem cell23_4149593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_4149593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149593 prefixEnd_4149593 := by exact prefixLift 4149593
  have htrace : WordTrace (prefixWord ++ tailWord_4149593) baseStart_4149593 baseEnd_4149593 := by
    simpa [prefixWord, tailWord_4149593, baseEnd_4149593] using wordTrace_append hprefix tailTrace_4149593
  have hstable : (prefixWord ++ tailWord_4149593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149593).length < 2 ^ (prefixWord ++ tailWord_4149593).sum := by decide
  have hdescent : baseEnd_4149593 < baseStart_4149593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149610 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4149610 : Nat := 118140960795 + 4149610 * 2 ^ 59
def prefixEnd_4149610 : Nat := 4983230072969 + 3 ^ 40 * 4149610 * 2
def baseEnd_4149610 : Nat := 2130744458703614865491297

theorem tailTrace_4149610 : CollatzResearch.WordTrace tailWord_4149610 prefixEnd_4149610 2130744458703614865491297 := by
  unfold tailWord_4149610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37837177624169785452715571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100899140331119427873908189 37837177624169785452715571)
  ·
    refine ⟨56755766436254678179073357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37837177624169785452715571 56755766436254678179073357)
    ·
      refine ⟨21283412413595504317152509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56755766436254678179073357 21283412413595504317152509)
      ·
        refine ⟨7981279655098314118932191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21283412413595504317152509 7981279655098314118932191)
        ·
          refine ⟨11971919482647471178398287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981279655098314118932191 11971919482647471178398287)
          ·
            refine ⟨17957879223971206767597431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11971919482647471178398287 17957879223971206767597431)
            ·
              refine ⟨26936818835956810151396147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17957879223971206767597431 26936818835956810151396147)
              ·
                refine ⟨40405228253935215227094221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26936818835956810151396147 40405228253935215227094221)
                ·
                  refine ⟨15151960595225705710160333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40405228253935215227094221 15151960595225705710160333)
                  ·
                    refine ⟨5681985223209639641310125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15151960595225705710160333 5681985223209639641310125)
                    ·
                      refine ⟨2130744458703614865491297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5681985223209639641310125 2130744458703614865491297)
                      ·
                        rfl

theorem cell23_4149610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4149610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149610 prefixEnd_4149610 := by exact prefixLift 4149610
  have htrace : WordTrace (prefixWord ++ tailWord_4149610) baseStart_4149610 baseEnd_4149610 := by
    simpa [prefixWord, tailWord_4149610, baseEnd_4149610] using wordTrace_append hprefix tailTrace_4149610
  have hstable : (prefixWord ++ tailWord_4149610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149610).length < 2 ^ (prefixWord ++ tailWord_4149610).sum := by decide
  have hdescent : baseEnd_4149610 < baseStart_4149610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149627 : List Nat := [1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 3]
def baseStart_4149627 : Nat := 118140960795 + 4149627 * 2 ^ 59
def prefixEnd_4149627 : Nat := 4983230072969 + 3 ^ 40 * 4149627 * 2
def baseEnd_4149627 : Nat := 2130753187874741298978719

theorem tailTrace_4149627 : CollatzResearch.WordTrace tailWord_4149627 prefixEnd_4149627 2130753187874741298978719 := by
  unfold tailWord_4149627
  simp only [CollatzResearch.WordTrace]
  refine ⟨151349330537617553714231135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100899553691745035809487423 151349330537617553714231135)
  ·
    refine ⟨227023995806426330571346703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151349330537617553714231135 227023995806426330571346703)
    ·
      refine ⟨340535993709639495857020055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227023995806426330571346703 340535993709639495857020055)
      ·
        refine ⟨510803990564459243785530083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340535993709639495857020055 510803990564459243785530083)
        ·
          refine ⟨766205985846688865678295125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510803990564459243785530083 766205985846688865678295125)
          ·
            refine ⟨8978976396640885144667521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 766205985846688865678295125 8978976396640885144667521)
            ·
              refine ⟨6734232297480663858500641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8978976396640885144667521 6734232297480663858500641)
              ·
                refine ⟨5050674223110497893875481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734232297480663858500641 5050674223110497893875481)
                ·
                  refine ⟨3788005667332873420406611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5050674223110497893875481 3788005667332873420406611)
                  ·
                    refine ⟨5682008500999310130609917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3788005667332873420406611 5682008500999310130609917)
                    ·
                      refine ⟨2130753187874741298978719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5682008500999310130609917 2130753187874741298978719)
                      ·
                        rfl

theorem cell23_4149627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 1, 3].length) (baseStart_4149627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149627 prefixEnd_4149627 := by exact prefixLift 4149627
  have htrace : WordTrace (prefixWord ++ tailWord_4149627) baseStart_4149627 baseEnd_4149627 := by
    simpa [prefixWord, tailWord_4149627, baseEnd_4149627] using wordTrace_append hprefix tailTrace_4149627
  have hstable : (prefixWord ++ tailWord_4149627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149627).length < 2 ^ (prefixWord ++ tailWord_4149627).sum := by decide
  have hdescent : baseEnd_4149627 < baseStart_4149627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149634 : List Nat := [3, 4, 2, 1, 3, 1, 1, 8]
def baseStart_4149634 : Nat := 118140960795 + 4149634 * 2 ^ 59
def prefixEnd_4149634 : Nat := 4983230072969 + 3 ^ 40 * 4149634 * 2
def baseEnd_4149634 : Nat := 78916917860715658207081

theorem tailTrace_4149634 : CollatzResearch.WordTrace tailWord_4149634 prefixEnd_4149634 78916917860715658207081 := by
  unfold tailWord_4149634
  simp only [CollatzResearch.WordTrace]
  refine ⟨37837396462148048477433989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100899723899061462606490637 37837396462148048477433989)
  ·
    refine ⟨7094511836652759089518873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37837396462148048477433989 7094511836652759089518873)
    ·
      refine ⟨5320883877489569317139155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7094511836652759089518873 5320883877489569317139155)
      ·
        refine ⟨7981325816234353975708733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5320883877489569317139155 7981325816234353975708733)
        ·
          refine ⟨2992997181087882740890775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7981325816234353975708733 2992997181087882740890775)
          ·
            refine ⟨4489495771631824111336163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2992997181087882740890775 4489495771631824111336163)
            ·
              refine ⟨6734243657447736167004245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489495771631824111336163 6734243657447736167004245)
              ·
                refine ⟨78916917860715658207081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6734243657447736167004245 78916917860715658207081)
                ·
                  rfl

theorem cell23_4149634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_4149634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149634 prefixEnd_4149634 := by exact prefixLift 4149634
  have htrace : WordTrace (prefixWord ++ tailWord_4149634) baseStart_4149634 baseEnd_4149634 := by
    simpa [prefixWord, tailWord_4149634, baseEnd_4149634] using wordTrace_append hprefix tailTrace_4149634
  have hstable : (prefixWord ++ tailWord_4149634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149634).length < 2 ^ (prefixWord ++ tailWord_4149634).sum := by decide
  have hdescent : baseEnd_4149634 < baseStart_4149634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149643 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 2, 6]
def baseStart_4149643 : Nat := 118140960795 + 4149643 * 2 ^ 59
def prefixEnd_4149643 : Nat := 4983230072969 + 3 ^ 40 * 4149643 * 2
def baseEnd_4149643 : Nat := 710253801188404412126215

theorem tailTrace_4149643 : CollatzResearch.WordTrace tailWord_4149643 prefixEnd_4149643 710253801188404412126215 := by
  unfold tailWord_4149643
  simp only [CollatzResearch.WordTrace]
  refine ⟨151349914105559588446813583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100899942737039725631209055 151349914105559588446813583)
  ·
    refine ⟨227024871158339382670220375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151349914105559588446813583 227024871158339382670220375)
    ·
      refine ⟨340537306737509074005330563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227024871158339382670220375 340537306737509074005330563)
      ·
        refine ⟨510805960106263611007995845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340537306737509074005330563 510805960106263611007995845)
        ·
          refine ⟨95776117519924427063999221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510805960106263611007995845 95776117519924427063999221)
          ·
            refine ⟨8979011017492915037249927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95776117519924427063999221 8979011017492915037249927)
            ·
              refine ⟨13468516526239372555874891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8979011017492915037249927 13468516526239372555874891)
              ·
                refine ⟨20202774789359058833812337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13468516526239372555874891 20202774789359058833812337)
                ·
                  refine ⟨15152081092019294125359253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20202774789359058833812337 15152081092019294125359253)
                  ·
                    refine ⟨710253801188404412126215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15152081092019294125359253 710253801188404412126215)
                    ·
                      rfl

theorem cell23_4149643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 6].length) (baseStart_4149643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149643 prefixEnd_4149643 := by exact prefixLift 4149643
  have htrace : WordTrace (prefixWord ++ tailWord_4149643) baseStart_4149643 baseEnd_4149643 := by
    simpa [prefixWord, tailWord_4149643, baseEnd_4149643] using wordTrace_append hprefix tailTrace_4149643
  have hstable : (prefixWord ++ tailWord_4149643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149643).length < 2 ^ (prefixWord ++ tailWord_4149643).sum := by decide
  have hdescent : baseEnd_4149643 < baseStart_4149643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149653 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 3]
def baseStart_4149653 : Nat := 118140960795 + 4149653 * 2 ^ 59
def prefixEnd_4149653 : Nat := 4983230072969 + 3 ^ 40 * 4149653 * 2
def baseEnd_4149653 : Nat := 2130766538371758197253599

theorem tailTrace_4149653 : CollatzResearch.WordTrace tailWord_4149653 prefixEnd_4149653 2130766538371758197253599 := by
  unfold tailWord_4149653
  simp only [CollatzResearch.WordTrace]
  refine ⟨151350278835523360154677613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100900185890348906769785075 151350278835523360154677613)
  ·
    refine ⟨56756354563321260058004105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151350278835523360154677613 56756354563321260058004105)
    ·
      refine ⟨42567265922490945043503079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56756354563321260058004105 42567265922490945043503079)
      ·
        refine ⟨63850898883736417565254619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42567265922490945043503079 63850898883736417565254619)
        ·
          refine ⟨95776348325604626347881929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63850898883736417565254619 95776348325604626347881929)
          ·
            refine ⟨71832261244203469760911447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95776348325604626347881929 71832261244203469760911447)
            ·
              refine ⟨107748391866305204641367171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71832261244203469760911447 107748391866305204641367171)
              ·
                refine ⟨161622587799457806962050757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107748391866305204641367171 161622587799457806962050757)
                ·
                  refine ⟨30304235212398338805384517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161622587799457806962050757 30304235212398338805384517)
                  ·
                    refine ⟨5682044102324688526009597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30304235212398338805384517 5682044102324688526009597)
                    ·
                      refine ⟨2130766538371758197253599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5682044102324688526009597 2130766538371758197253599)
                      ·
                        rfl

theorem cell23_4149653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_4149653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149653 prefixEnd_4149653 := by exact prefixLift 4149653
  have htrace : WordTrace (prefixWord ++ tailWord_4149653) baseStart_4149653 baseEnd_4149653 := by
    simpa [prefixWord, tailWord_4149653, baseEnd_4149653] using wordTrace_append hprefix tailTrace_4149653
  have hstable : (prefixWord ++ tailWord_4149653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149653).length < 2 ^ (prefixWord ++ tailWord_4149653).sum := by decide
  have hdescent : baseEnd_4149653 < baseStart_4149653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149663 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_4149663 : Nat := 118140960795 + 4149663 * 2 ^ 59
def prefixEnd_4149663 : Nat := 4983230072969 + 3 ^ 40 * 4149663 * 2
def baseEnd_4149663 : Nat := 2130771673178303158128553

theorem tailTrace_4149663 : CollatzResearch.WordTrace tailWord_4149663 prefixEnd_4149663 2130771673178303158128553 := by
  unfold tailWord_4149663
  simp only [CollatzResearch.WordTrace]
  refine ⟨151350643565487131862541643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100900429043658087908361095 151350643565487131862541643)
  ·
    refine ⟨227025965348230697793812465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151350643565487131862541643 227025965348230697793812465)
    ·
      refine ⟨170269474011173023345359349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227025965348230697793812465 170269474011173023345359349)
      ·
        refine ⟨15962763188547470938627439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170269474011173023345359349 15962763188547470938627439)
        ·
          refine ⟨23944144782821206407941159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962763188547470938627439 23944144782821206407941159)
          ·
            refine ⟨35916217174231809611911739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23944144782821206407941159 35916217174231809611911739)
            ·
              refine ⟨53874325761347714417867609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35916217174231809611911739 53874325761347714417867609)
              ·
                refine ⟨40405744321010785813400707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53874325761347714417867609 40405744321010785813400707)
                ·
                  refine ⟨60608616481516178720101061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40405744321010785813400707 60608616481516178720101061)
                  ·
                    refine ⟨11364115590284283510018949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60608616481516178720101061 11364115590284283510018949)
                    ·
                      refine ⟨2130771673178303158128553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11364115590284283510018949 2130771673178303158128553)
                      ·
                        rfl

theorem cell23_4149663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_4149663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149663 prefixEnd_4149663 := by exact prefixLift 4149663
  have htrace : WordTrace (prefixWord ++ tailWord_4149663) baseStart_4149663 baseEnd_4149663 := by
    simpa [prefixWord, tailWord_4149663, baseEnd_4149663] using wordTrace_append hprefix tailTrace_4149663
  have hstable : (prefixWord ++ tailWord_4149663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149663).length < 2 ^ (prefixWord ++ tailWord_4149663).sum := by decide
  have hdescent : baseEnd_4149663 < baseStart_4149663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149671 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 1, 3, 2]
def baseStart_4149671 : Nat := 118140960795 + 4149671 * 2 ^ 59
def prefixEnd_4149671 : Nat := 4983230072969 + 3 ^ 40 * 4149671 * 2
def baseEnd_4149671 : Nat := 2130775781023539126828517

theorem tailTrace_4149671 : CollatzResearch.WordTrace tailWord_4149671 prefixEnd_4149671 2130775781023539126828517 := by
  unfold tailWord_4149671
  simp only [CollatzResearch.WordTrace]
  refine ⟨151350935349458149228832867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100900623566305432819221911 151350935349458149228832867)
  ·
    refine ⟨227026403024187223843249301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151350935349458149228832867 227026403024187223843249301)
    ·
      refine ⟨10641862641758776117652311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 227026403024187223843249301 10641862641758776117652311)
      ·
        refine ⟨15962793962638164176478467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10641862641758776117652311 15962793962638164176478467)
        ·
          refine ⟨23944190943957246264717701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15962793962638164176478467 23944190943957246264717701)
          ·
            refine ⟨4489535801991983674634569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23944190943957246264717701 4489535801991983674634569)
            ·
              refine ⟨3367151851493987755975927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4489535801991983674634569 3367151851493987755975927)
              ·
                refine ⟨5050727777240981633963891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367151851493987755975927 5050727777240981633963891)
                ·
                  refine ⟨7576091665861472450945837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050727777240981633963891 7576091665861472450945837)
                  ·
                    refine ⟨2841034374698052169104689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7576091665861472450945837 2841034374698052169104689)
                    ·
                      refine ⟨2130775781023539126828517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841034374698052169104689 2130775781023539126828517)
                      ·
                        rfl

theorem cell23_4149671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_4149671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149671 prefixEnd_4149671 := by exact prefixLift 4149671
  have htrace : WordTrace (prefixWord ++ tailWord_4149671) baseStart_4149671 baseEnd_4149671 := by
    simpa [prefixWord, tailWord_4149671, baseEnd_4149671] using wordTrace_append hprefix tailTrace_4149671
  have hstable : (prefixWord ++ tailWord_4149671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149671).length < 2 ^ (prefixWord ++ tailWord_4149671).sum := by decide
  have hdescent : baseEnd_4149671 < baseStart_4149671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149703 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 1, 7]
def baseStart_4149703 : Nat := 118140960795 + 4149703 * 2 ^ 59
def prefixEnd_4149703 : Nat := 4983230072969 + 3 ^ 40 * 4149703 * 2
def baseEnd_4149703 : Nat := 710264070801494333876123

theorem tailTrace_4149703 : CollatzResearch.WordTrace tailWord_4149703 prefixEnd_4149703 710264070801494333876123 := by
  unfold tailWord_4149703
  simp only [CollatzResearch.WordTrace]
  refine ⟨151352102485342218693997763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100901401656894812462665175 151352102485342218693997763)
  ·
    refine ⟨227028153728013328040996645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151352102485342218693997763 227028153728013328040996645)
    ·
      refine ⟨42567778824002499007686871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 227028153728013328040996645 42567778824002499007686871)
      ·
        refine ⟨63851668236003748511530307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42567778824002499007686871 63851668236003748511530307)
        ·
          refine ⟨95777502354005622767295461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63851668236003748511530307 95777502354005622767295461)
          ·
            refine ⟨17958281691376054268867899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95777502354005622767295461 17958281691376054268867899)
            ·
              refine ⟨26937422537064081403301849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17958281691376054268867899 26937422537064081403301849)
              ·
                refine ⟨20203066902798061052476387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26937422537064081403301849 20203066902798061052476387)
                ·
                  refine ⟨30304600354197091578714581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20203066902798061052476387 30304600354197091578714581)
                  ·
                    refine ⟨710264070801494333876123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30304600354197091578714581 710264070801494333876123)
                    ·
                      rfl

theorem cell23_4149703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_4149703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149703 prefixEnd_4149703 := by exact prefixLift 4149703
  have htrace : WordTrace (prefixWord ++ tailWord_4149703) baseStart_4149703 baseEnd_4149703 := by
    simpa [prefixWord, tailWord_4149703, baseEnd_4149703] using wordTrace_append hprefix tailTrace_4149703
  have hstable : (prefixWord ++ tailWord_4149703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149703).length < 2 ^ (prefixWord ++ tailWord_4149703).sum := by decide
  have hdescent : baseEnd_4149703 < baseStart_4149703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149740 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_4149740 : Nat := 118140960795 + 4149740 * 2 ^ 59
def prefixEnd_4149740 : Nat := 4983230072969 + 3 ^ 40 * 4149740 * 2
def baseEnd_4149740 : Nat := 2130811211188699356865699

theorem tailTrace_4149740 : CollatzResearch.WordTrace tailWord_4149740 prefixEnd_4149740 2130811211188699356865699 := by
  unfold tailWord_4149740
  simp only [CollatzResearch.WordTrace]
  refine ⟨75676725993104087006547337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100902301324138782675396449 75676725993104087006547337)
  ·
    refine ⟨56757544494828065254910503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75676725993104087006547337 56757544494828065254910503)
    ·
      refine ⟨85136316742242097882365755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56757544494828065254910503 85136316742242097882365755)
      ·
        refine ⟨127704475113363146823548633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85136316742242097882365755 127704475113363146823548633)
        ·
          refine ⟨95778356335022360117661475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127704475113363146823548633 95778356335022360117661475)
          ·
            refine ⟨143667534502533540176492213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95778356335022360117661475 143667534502533540176492213)
            ·
              refine ⟨13468831359612519391546145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143667534502533540176492213 13468831359612519391546145)
              ·
                refine ⟨10101623519709389543659609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13468831359612519391546145 10101623519709389543659609)
                ·
                  refine ⟨7576217639782042157744707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10101623519709389543659609 7576217639782042157744707)
                  ·
                    refine ⟨11364326459673063236617061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576217639782042157744707 11364326459673063236617061)
                    ·
                      refine ⟨2130811211188699356865699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11364326459673063236617061 2130811211188699356865699)
                      ·
                        rfl

theorem cell23_4149740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_4149740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149740 prefixEnd_4149740 := by exact prefixLift 4149740
  have htrace : WordTrace (prefixWord ++ tailWord_4149740) baseStart_4149740 baseEnd_4149740 := by
    simpa [prefixWord, tailWord_4149740, baseEnd_4149740] using wordTrace_append hprefix tailTrace_4149740
  have hstable : (prefixWord ++ tailWord_4149740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149740).length < 2 ^ (prefixWord ++ tailWord_4149740).sum := by decide
  have hdescent : baseEnd_4149740 < baseStart_4149740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149753 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_4149753 : Nat := 118140960795 + 4149753 * 2 ^ 59
def prefixEnd_4149753 : Nat := 4983230072969 + 3 ^ 40 * 4149753 * 2
def baseEnd_4149753 : Nat := 2130817886437207806003139

theorem tailTrace_4149753 : CollatzResearch.WordTrace tailWord_4149753 prefixEnd_4149753 2130817886437207806003139 := by
  unfold tailWord_4149753
  simp only [CollatzResearch.WordTrace]
  refine ⟨151353926135161077233317913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100902617423440718155545275 151353926135161077233317913)
  ·
    refine ⟨113515444601370807924988435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151353926135161077233317913 113515444601370807924988435)
    ·
      refine ⟨170273166902056211887482653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113515444601370807924988435 170273166902056211887482653)
      ·
        refine ⟨63852437588271079457805995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170273166902056211887482653 63852437588271079457805995)
        ·
          refine ⟨95778656382406619186708993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63852437588271079457805995 95778656382406619186708993)
          ·
            refine ⟨71833992286804964390031745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95778656382406619186708993 71833992286804964390031745)
            ·
              refine ⟨53875494215103723292523809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71833992286804964390031745 53875494215103723292523809)
              ·
                refine ⟨40406620661327792469392857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53875494215103723292523809 40406620661327792469392857)
                ·
                  refine ⟨30304965495995844352044643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40406620661327792469392857 30304965495995844352044643)
                  ·
                    refine ⟨45457448243993766528066965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30304965495995844352044643 45457448243993766528066965)
                    ·
                      refine ⟨2130817886437207806003139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45457448243993766528066965 2130817886437207806003139)
                      ·
                        rfl

theorem cell23_4149753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_4149753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149753 prefixEnd_4149753 := by exact prefixLift 4149753
  have htrace : WordTrace (prefixWord ++ tailWord_4149753) baseStart_4149753 baseEnd_4149753 := by
    simpa [prefixWord, tailWord_4149753, baseEnd_4149753] using wordTrace_append hprefix tailTrace_4149753
  have hstable : (prefixWord ++ tailWord_4149753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149753).length < 2 ^ (prefixWord ++ tailWord_4149753).sum := by decide
  have hdescent : baseEnd_4149753 < baseStart_4149753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149803 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_4149803 : Nat := 118140960795 + 4149803 * 2 ^ 59
def prefixEnd_4149803 : Nat := 4983230072969 + 3 ^ 40 * 4149803 * 2
def baseEnd_4149803 : Nat := 2130843560469932610377909

theorem tailTrace_4149803 : CollatzResearch.WordTrace tailWord_4149803 prefixEnd_4149803 2130843560469932610377909 := by
  unfold tailWord_4149803
  simp only [CollatzResearch.WordTrace]
  refine ⟨151355749784979935772638063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100903833189986623848425375 151355749784979935772638063)
  ·
    refine ⟨227033624677469903658957095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151355749784979935772638063 227033624677469903658957095)
    ·
      refine ⟨340550437016204855488435643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227033624677469903658957095 340550437016204855488435643)
      ·
        refine ⟨510825655524307283232653465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340550437016204855488435643 510825655524307283232653465)
        ·
          refine ⟨383119241643230462424490099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510825655524307283232653465 383119241643230462424490099)
          ·
            refine ⟨574678862464845693636735149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383119241643230462424490099 574678862464845693636735149)
            ·
              refine ⟨215504573424317135113775681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 574678862464845693636735149 215504573424317135113775681)
              ·
                refine ⟨161628430068237851335331761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215504573424317135113775681 161628430068237851335331761)
                ·
                  refine ⟨121221322551178388501498821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161628430068237851335331761 121221322551178388501498821)
                  ·
                    refine ⟨22728997978345947844031029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121221322551178388501498821 22728997978345947844031029)
                    ·
                      refine ⟨2130843560469932610377909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22728997978345947844031029 2130843560469932610377909)
                      ·
                        rfl

theorem cell23_4149803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_4149803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149803 prefixEnd_4149803 := by exact prefixLift 4149803
  have htrace : WordTrace (prefixWord ++ tailWord_4149803) baseStart_4149803 baseEnd_4149803 := by
    simpa [prefixWord, tailWord_4149803, baseEnd_4149803] using wordTrace_append hprefix tailTrace_4149803
  have hstable : (prefixWord ++ tailWord_4149803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149803).length < 2 ^ (prefixWord ++ tailWord_4149803).sum := by decide
  have hdescent : baseEnd_4149803 < baseStart_4149803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149810 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_4149810 : Nat := 118140960795 + 4149810 * 2 ^ 59
def prefixEnd_4149810 : Nat := 4983230072969 + 3 ^ 40 * 4149810 * 2
def baseEnd_4149810 : Nat := 710282384944838027663459

theorem tailTrace_4149810 : CollatzResearch.WordTrace tailWord_4149810 prefixEnd_4149810 710282384944838027663459 := by
  unfold tailWord_4149810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839001273988643992035721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100904003397303050645428589 37839001273988643992035721)
  ·
    refine ⟨28379250955491482994026791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37839001273988643992035721 28379250955491482994026791)
    ·
      refine ⟨42568876433237224491040187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28379250955491482994026791 42568876433237224491040187)
      ·
        refine ⟨63853314649855836736560281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42568876433237224491040187 63853314649855836736560281)
        ·
          refine ⟨47889985987391877552420211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63853314649855836736560281 47889985987391877552420211)
          ·
            refine ⟨71834978981087816328630317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47889985987391877552420211 71834978981087816328630317)
            ·
              refine ⟨26938117117907931123236369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71834978981087816328630317 26938117117907931123236369)
              ·
                refine ⟨20203587838430948342427277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26938117117907931123236369 20203587838430948342427277)
                ·
                  refine ⟨7576345439411605628410229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20203587838430948342427277 7576345439411605628410229)
                  ·
                    refine ⟨710282384944838027663459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7576345439411605628410229 710282384944838027663459)
                    ·
                      rfl

theorem cell23_4149810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_4149810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149810 prefixEnd_4149810 := by exact prefixLift 4149810
  have htrace : WordTrace (prefixWord ++ tailWord_4149810) baseStart_4149810 baseEnd_4149810 := by
    simpa [prefixWord, tailWord_4149810, baseEnd_4149810] using wordTrace_append hprefix tailTrace_4149810
  have hstable : (prefixWord ++ tailWord_4149810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149810).length < 2 ^ (prefixWord ++ tailWord_4149810).sum := by decide
  have hdescent : baseEnd_4149810 < baseStart_4149810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149817 : List Nat := [1, 2, 1, 5, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4149817 : Nat := 118140960795 + 4149817 * 2 ^ 59
def prefixEnd_4149817 : Nat := 4983230072969 + 3 ^ 40 * 4149817 * 2
def baseEnd_4149817 : Nat := 2130850749199095555602845

theorem tailTrace_4149817 : CollatzResearch.WordTrace tailWord_4149817 prefixEnd_4149817 2130850749199095555602845 := by
  unfold tailWord_4149817
  simp only [CollatzResearch.WordTrace]
  refine ⟨151356260406929216163647705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100904173604619477442431803 151356260406929216163647705)
  ·
    refine ⟨113517195305196912122735779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151356260406929216163647705 113517195305196912122735779)
    ·
      refine ⟨170275792957795368184103669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113517195305196912122735779 170275792957795368184103669)
      ·
        refine ⟨15963355589793315767259719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170275792957795368184103669 15963355589793315767259719)
        ·
          refine ⟨23945033384689973650889579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15963355589793315767259719 23945033384689973650889579)
          ·
            refine ⟨35917550077034960476334369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23945033384689973650889579 35917550077034960476334369)
            ·
              refine ⟨26938162557776220357250777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35917550077034960476334369 26938162557776220357250777)
              ·
                refine ⟨20203621918332165267938083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26938162557776220357250777 20203621918332165267938083)
                ·
                  refine ⟨30305432877498247901907125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20203621918332165267938083 30305432877498247901907125)
                  ·
                    refine ⟨2841134332265460740803793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30305432877498247901907125 2841134332265460740803793)
                    ·
                      refine ⟨2130850749199095555602845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841134332265460740803793 2130850749199095555602845)
                      ·
                        rfl

theorem cell23_4149817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4149817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149817 prefixEnd_4149817 := by exact prefixLift 4149817
  have htrace : WordTrace (prefixWord ++ tailWord_4149817) baseStart_4149817 baseEnd_4149817 := by
    simpa [prefixWord, tailWord_4149817, baseEnd_4149817] using wordTrace_append hprefix tailTrace_4149817
  have hstable : (prefixWord ++ tailWord_4149817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149817).length < 2 ^ (prefixWord ++ tailWord_4149817).sum := by decide
  have hdescent : baseEnd_4149817 < baseStart_4149817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149834 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2]
def baseStart_4149834 : Nat := 118140960795 + 4149834 * 2 ^ 59
def prefixEnd_4149834 : Nat := 4983230072969 + 3 ^ 40 * 4149834 * 2
def baseEnd_4149834 : Nat := 2130859478370221989090267

theorem tailTrace_4149834 : CollatzResearch.WordTrace tailWord_4149834 prefixEnd_4149834 2130859478370221989090267 := by
  unfold tailWord_4149834
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839220111966907016754139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100904586965245085378011037 37839220111966907016754139)
  ·
    refine ⟨56758830167950360525131209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37839220111966907016754139 56758830167950360525131209)
    ·
      refine ⟨42569122625962770393848407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56758830167950360525131209 42569122625962770393848407)
      ·
        refine ⟨63853683938944155590772611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42569122625962770393848407 63853683938944155590772611)
        ·
          refine ⟨95780525908416233386158917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63853683938944155590772611 95780525908416233386158917)
          ·
            refine ⟨17958848607828043759904797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95780525908416233386158917 17958848607828043759904797)
            ·
              refine ⟨6734568227935516409964299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17958848607828043759904797 6734568227935516409964299)
              ·
                refine ⟨10101852341903274614946449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734568227935516409964299 10101852341903274614946449)
                ·
                  refine ⟨7576389256427455961209837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10101852341903274614946449 7576389256427455961209837)
                  ·
                    refine ⟨2841145971160295985453689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7576389256427455961209837 2841145971160295985453689)
                    ·
                      refine ⟨2130859478370221989090267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841145971160295985453689 2130859478370221989090267)
                      ·
                        rfl

theorem cell23_4149834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_4149834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149834 prefixEnd_4149834 := by exact prefixLift 4149834
  have htrace : WordTrace (prefixWord ++ tailWord_4149834) baseStart_4149834 baseEnd_4149834 := by
    simpa [prefixWord, tailWord_4149834, baseEnd_4149834] using wordTrace_append hprefix tailTrace_4149834
  have hstable : (prefixWord ++ tailWord_4149834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149834).length < 2 ^ (prefixWord ++ tailWord_4149834).sum := by decide
  have hdescent : baseEnd_4149834 < baseStart_4149834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149841 : List Nat := [1, 2, 2, 1, 3, 4, 2, 3, 1, 1, 3]
def baseStart_4149841 : Nat := 118140960795 + 4149841 * 2 ^ 59
def prefixEnd_4149841 : Nat := 4983230072969 + 3 ^ 40 * 4149841 * 2
def baseEnd_4149841 : Nat := 2130863072734803461702735

theorem tailTrace_4149841 : CollatzResearch.WordTrace tailWord_4149841 prefixEnd_4149841 2130863072734803461702735 := by
  unfold tailWord_4149841
  simp only [CollatzResearch.WordTrace]
  refine ⟨151357135758842268262521377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100904757172561512175014251 151357135758842268262521377)
  ·
    refine ⟨113517851819131701196891033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151357135758842268262521377 113517851819131701196891033)
    ·
      refine ⟨85138388864348775897668275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113517851819131701196891033 85138388864348775897668275)
      ·
        refine ⟨127707583296523163846502413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85138388864348775897668275 127707583296523163846502413)
        ·
          refine ⟨47890343736196186442438405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127707583296523163846502413 47890343736196186442438405)
          ·
            refine ⟨8979439450536784957957201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47890343736196186442438405 8979439450536784957957201)
            ·
              refine ⟨6734579587902588718467901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979439450536784957957201 6734579587902588718467901)
              ·
                refine ⟨2525467345463470769425463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6734579587902588718467901 2525467345463470769425463)
                ·
                  refine ⟨3788201018195206154138195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525467345463470769425463 3788201018195206154138195)
                  ·
                    refine ⟨5682301527292809231207293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3788201018195206154138195 5682301527292809231207293)
                    ·
                      refine ⟨2130863072734803461702735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5682301527292809231207293 2130863072734803461702735)
                      ·
                        rfl

theorem cell23_4149841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 3, 1, 1, 3].length) (baseStart_4149841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149841 prefixEnd_4149841 := by exact prefixLift 4149841
  have htrace : WordTrace (prefixWord ++ tailWord_4149841) baseStart_4149841 baseEnd_4149841 := by
    simpa [prefixWord, tailWord_4149841, baseEnd_4149841] using wordTrace_append hprefix tailTrace_4149841
  have hstable : (prefixWord ++ tailWord_4149841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149841).length < 2 ^ (prefixWord ++ tailWord_4149841).sum := by decide
  have hdescent : baseEnd_4149841 < baseStart_4149841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149844 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 1, 5]
def baseStart_4149844 : Nat := 118140960795 + 4149844 * 2 ^ 59
def prefixEnd_4149844 : Nat := 4983230072969 + 3 ^ 40 * 4149844 * 2
def baseEnd_4149844 : Nat := 710288204392255649988407

theorem tailTrace_4149844 : CollatzResearch.WordTrace tailWord_4149844 prefixEnd_4149844 710288204392255649988407 := by
  unfold tailWord_4149844
  simp only [CollatzResearch.WordTrace]
  refine ⟨75678622588915699887440293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100904830118554266516587057 75678622588915699887440293)
  ·
    refine ⟨14189741735421693728895055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75678622588915699887440293 14189741735421693728895055)
    ·
      refine ⟨21284612603132540593342583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14189741735421693728895055 21284612603132540593342583)
      ·
        refine ⟨31926918904698810890013875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21284612603132540593342583 31926918904698810890013875)
        ·
          refine ⟨47890378357048216335020813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31926918904698810890013875 47890378357048216335020813)
          ·
            refine ⟨17958891883893081125632805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47890378357048216335020813 17958891883893081125632805)
            ·
              refine ⟨3367292228229952711056151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17958891883893081125632805 3367292228229952711056151)
              ·
                refine ⟨5050938342344929066584227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367292228229952711056151 5050938342344929066584227)
                ·
                  refine ⟨7576407513517393599876341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050938342344929066584227 7576407513517393599876341)
                  ·
                    refine ⟨710288204392255649988407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7576407513517393599876341 710288204392255649988407)
                    ·
                      rfl

theorem cell23_4149844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_4149844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149844 prefixEnd_4149844 := by exact prefixLift 4149844
  have htrace : WordTrace (prefixWord ++ tailWord_4149844) baseStart_4149844 baseEnd_4149844 := by
    simpa [prefixWord, tailWord_4149844, baseEnd_4149844] using wordTrace_append hprefix tailTrace_4149844
  have hstable : (prefixWord ++ tailWord_4149844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149844).length < 2 ^ (prefixWord ++ tailWord_4149844).sum := by decide
  have hdescent : baseEnd_4149844 < baseStart_4149844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149847 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 4]
def baseStart_4149847 : Nat := 118140960795 + 4149847 * 2 ^ 59
def prefixEnd_4149847 : Nat := 4983230072969 + 3 ^ 40 * 4149847 * 2
def baseEnd_4149847 : Nat := 2130866153618730438227707

theorem tailTrace_4149847 : CollatzResearch.WordTrace tailWord_4149847 prefixEnd_4149847 2130866153618730438227707 := by
  unfold tailWord_4149847
  simp only [CollatzResearch.WordTrace]
  refine ⟨151357354596820531287239795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100904903064547020858159863 151357354596820531287239795)
  ·
    refine ⟨227036031895230796930859693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151357354596820531287239795 227036031895230796930859693)
    ·
      refine ⟨85138511960711548849072385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227036031895230796930859693 85138511960711548849072385)
      ·
        refine ⟨63853883970533661636804289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85138511960711548849072385 63853883970533661636804289)
        ·
          refine ⟨47890412977900246227603217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63853883970533661636804289 47890412977900246227603217)
          ·
            refine ⟨35917809733425184670702413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47890412977900246227603217 35917809733425184670702413)
            ·
              refine ⟨13469178650034444251513405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35917809733425184670702413 13469178650034444251513405)
              ·
                refine ⟨5050941993762916594317527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13469178650034444251513405 5050941993762916594317527)
                ·
                  refine ⟨7576412990644374891476291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5050941993762916594317527 7576412990644374891476291)
                  ·
                    refine ⟨11364619485966562337214437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576412990644374891476291 11364619485966562337214437)
                    ·
                      refine ⟨2130866153618730438227707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11364619485966562337214437 2130866153618730438227707)
                      ·
                        rfl

theorem cell23_4149847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_4149847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149847 prefixEnd_4149847 := by exact prefixLift 4149847
  have htrace : WordTrace (prefixWord ++ tailWord_4149847) baseStart_4149847 baseEnd_4149847 := by
    simpa [prefixWord, tailWord_4149847, baseEnd_4149847] using wordTrace_append hprefix tailTrace_4149847
  have hstable : (prefixWord ++ tailWord_4149847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149847).length < 2 ^ (prefixWord ++ tailWord_4149847).sum := by decide
  have hdescent : baseEnd_4149847 < baseStart_4149847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149857 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 4, 4]
def baseStart_4149857 : Nat := 118140960795 + 4149857 * 2 ^ 59
def prefixEnd_4149857 : Nat := 4983230072969 + 3 ^ 40 * 4149857 * 2
def baseEnd_4149857 : Nat := 710290429475091799700887

theorem tailTrace_4149857 : CollatzResearch.WordTrace tailWord_4149857 prefixEnd_4149857 710290429475091799700887 := by
  unfold tailWord_4149857
  simp only [CollatzResearch.WordTrace]
  refine ⟨151357719326784302995103825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100905146217856201996735883 151357719326784302995103825)
  ·
    refine ⟨113518289495088227246327869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151357719326784302995103825 113518289495088227246327869)
    ·
      refine ⟨42569358560658085217372951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113518289495088227246327869 42569358560658085217372951)
      ·
        refine ⟨63854037840987127826059427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42569358560658085217372951 63854037840987127826059427)
        ·
          refine ⟨95781056761480691739089141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63854037840987127826059427 95781056761480691739089141)
          ·
            refine ⟨8979474071388814850539607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95781056761480691739089141 8979474071388814850539607)
            ·
              refine ⟨13469211107083222275809411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8979474071388814850539607 13469211107083222275809411)
              ·
                refine ⟨20203816660624833413714117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13469211107083222275809411 20203816660624833413714117)
                ·
                  refine ⟨3788215623867156265071397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20203816660624833413714117 3788215623867156265071397)
                  ·
                    refine ⟨710290429475091799700887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3788215623867156265071397 710290429475091799700887)
                    ·
                      rfl

theorem cell23_4149857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_4149857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149857 prefixEnd_4149857 := by exact prefixLift 4149857
  have htrace : WordTrace (prefixWord ++ tailWord_4149857) baseStart_4149857 baseEnd_4149857 := by
    simpa [prefixWord, tailWord_4149857, baseEnd_4149857] using wordTrace_append hprefix tailTrace_4149857
  have hstable : (prefixWord ++ tailWord_4149857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149857).length < 2 ^ (prefixWord ++ tailWord_4149857).sum := by decide
  have hdescent : baseEnd_4149857 < baseStart_4149857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149858 : List Nat := [3, 3, 2, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4149858 : Nat := 118140960795 + 4149858 * 2 ^ 59
def prefixEnd_4149858 : Nat := 4983230072969 + 3 ^ 40 * 4149858 * 2
def baseEnd_4149858 : Nat := 2130871801905929895190157

theorem tailTrace_4149858 : CollatzResearch.WordTrace tailWord_4149858 prefixEnd_4149858 2130871801905929895190157 := by
  unfold tailWord_4149858
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839438949945170041472557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100905170533187120110593485 37839438949945170041472557)
  ·
    refine ⟨14189789606229438765552209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37839438949945170041472557 14189789606229438765552209)
    ·
      refine ⟨10642342204672079074164157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14189789606229438765552209 10642342204672079074164157)
      ·
        refine ⟨3990878326752029652811559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10642342204672079074164157 3990878326752029652811559)
        ·
          refine ⟨5986317490128044479217339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3990878326752029652811559 5986317490128044479217339)
          ·
            refine ⟨8979476235192066718826009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986317490128044479217339 8979476235192066718826009)
            ·
              refine ⟨6734607176394050039119507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979476235192066718826009 6734607176394050039119507)
              ·
                refine ⟨10101910764591075058679261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734607176394050039119507 10101910764591075058679261)
                ·
                  refine ⟨3788216536721653147004723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10101910764591075058679261 3788216536721653147004723)
                  ·
                    refine ⟨5682324805082479720507085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3788216536721653147004723 5682324805082479720507085)
                    ·
                      refine ⟨2130871801905929895190157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5682324805082479720507085 2130871801905929895190157)
                      ·
                        rfl

theorem cell23_4149858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4149858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149858 prefixEnd_4149858 := by exact prefixLift 4149858
  have htrace : WordTrace (prefixWord ++ tailWord_4149858) baseStart_4149858 baseEnd_4149858 := by
    simpa [prefixWord, tailWord_4149858, baseEnd_4149858] using wordTrace_append hprefix tailTrace_4149858
  have hstable : (prefixWord ++ tailWord_4149858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149858).length < 2 ^ (prefixWord ++ tailWord_4149858).sum := by decide
  have hdescent : baseEnd_4149858 < baseStart_4149858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149860 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_4149860 : Nat := 118140960795 + 4149860 * 2 ^ 59
def prefixEnd_4149860 : Nat := 4983230072969 + 3 ^ 40 * 4149860 * 2
def baseEnd_4149860 : Nat := 2130872828867238887365147

theorem tailTrace_4149860 : CollatzResearch.WordTrace tailWord_4149860 prefixEnd_4149860 2130872828867238887365147 := by
  unfold tailWord_4149860
  simp only [CollatzResearch.WordTrace]
  refine ⟨75678914372886717253731517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100905219163848956338308689 75678914372886717253731517)
  ·
    refine ⟨28379592889832518970149319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75678914372886717253731517 28379592889832518970149319)
    ·
      refine ⟨42569389334748778455223979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28379592889832518970149319 42569389334748778455223979)
      ·
        refine ⟨63854084002123167682835969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42569389334748778455223979 63854084002123167682835969)
        ·
          refine ⟨47890563001592375762126977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63854084002123167682835969 47890563001592375762126977)
          ·
            refine ⟨35917922251194281821595233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47890563001592375762126977 35917922251194281821595233)
            ·
              refine ⟨26938441688395711366196425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35917922251194281821595233 26938441688395711366196425)
              ·
                refine ⟨20203831266296783524647319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26938441688395711366196425 20203831266296783524647319)
                ·
                  refine ⟨30305746899445175286970979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20203831266296783524647319 30305746899445175286970979)
                  ·
                    refine ⟨45458620349167762930456469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30305746899445175286970979 45458620349167762930456469)
                    ·
                      refine ⟨2130872828867238887365147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45458620349167762930456469 2130872828867238887365147)
                      ·
                        rfl

theorem cell23_4149860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_4149860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149860 prefixEnd_4149860 := by exact prefixLift 4149860
  have htrace : WordTrace (prefixWord ++ tailWord_4149860) baseStart_4149860 baseEnd_4149860 := by
    simpa [prefixWord, tailWord_4149860, baseEnd_4149860] using wordTrace_append hprefix tailTrace_4149860
  have hstable : (prefixWord ++ tailWord_4149860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149860).length < 2 ^ (prefixWord ++ tailWord_4149860).sum := by decide
  have hdescent : baseEnd_4149860 < baseStart_4149860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149874 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_4149874 : Nat := 118140960795 + 4149874 * 2 ^ 59
def prefixEnd_4149874 : Nat := 4983230072969 + 3 ^ 40 * 4149874 * 2
def baseEnd_4149874 : Nat := 710293339198800610863361

theorem tailTrace_4149874 : CollatzResearch.WordTrace tailWord_4149874 prefixEnd_4149874 710293339198800610863361 := by
  unfold tailWord_4149874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37839584841930678724618169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100905559578481809932315117 37839584841930678724618169)
  ·
    refine ⟨28379688631448009043463627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37839584841930678724618169 28379688631448009043463627)
    ·
      refine ⟨42569532947172013565195441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28379688631448009043463627 42569532947172013565195441)
      ·
        refine ⟨31927149710379010173896581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42569532947172013565195441 31927149710379010173896581)
        ·
          refine ⟨5986340570696064407605609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31927149710379010173896581 5986340570696064407605609)
          ·
            refine ⟨4489755428022048305704207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5986340570696064407605609 4489755428022048305704207)
            ·
              refine ⟨6734633142033072458556311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4489755428022048305704207 6734633142033072458556311)
              ·
                refine ⟨10101949713049608687834467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6734633142033072458556311 10101949713049608687834467)
                ·
                  refine ⟨15152924569574413031751701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10101949713049608687834467 15152924569574413031751701)
                  ·
                    refine ⟨710293339198800610863361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15152924569574413031751701 710293339198800610863361)
                    ·
                      rfl

theorem cell23_4149874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_4149874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149874 prefixEnd_4149874 := by exact prefixLift 4149874
  have htrace : WordTrace (prefixWord ++ tailWord_4149874) baseStart_4149874 baseEnd_4149874 := by
    simpa [prefixWord, tailWord_4149874, baseEnd_4149874] using wordTrace_append hprefix tailTrace_4149874
  have hstable : (prefixWord ++ tailWord_4149874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149874).length < 2 ^ (prefixWord ++ tailWord_4149874).sum := by decide
  have hdescent : baseEnd_4149874 < baseStart_4149874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149924 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_4149924 : Nat := 118140960795 + 4149924 * 2 ^ 59
def prefixEnd_4149924 : Nat := 4983230072969 + 3 ^ 40 * 4149924 * 2
def baseEnd_4149924 : Nat := 2130905691629126636964853

theorem tailTrace_4149924 : CollatzResearch.WordTrace tailWord_4149924 prefixEnd_4149924 2130905691629126636964853 := by
  unfold tailWord_4149924
  simp only [CollatzResearch.WordTrace]
  refine ⟨75680081508770786718896413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100906775345027715625195217 75680081508770786718896413)
  ·
    refine ⟨28380030565789045019586155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75680081508770786718896413 28380030565789045019586155)
    ·
      refine ⟨42570045848683567529379233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28380030565789045019586155 42570045848683567529379233)
      ·
        refine ⟨31927534386512675647034425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42570045848683567529379233 31927534386512675647034425)
        ·
          refine ⟨23945650789884506735275819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31927534386512675647034425 23945650789884506735275819)
          ·
            refine ⟨35918476184826760102913729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23945650789884506735275819 35918476184826760102913729)
            ·
              refine ⟨26938857138620070077185297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35918476184826760102913729 26938857138620070077185297)
              ·
                refine ⟨20204142853965052557888973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26938857138620070077185297 20204142853965052557888973)
                ·
                  refine ⟨7576553570236894709208365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20204142853965052557888973 7576553570236894709208365)
                  ·
                    refine ⟨2841207588838835515953137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7576553570236894709208365 2841207588838835515953137)
                    ·
                      refine ⟨2130905691629126636964853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841207588838835515953137 2130905691629126636964853)
                      ·
                        rfl

theorem cell23_4149924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_4149924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149924 prefixEnd_4149924 := by exact prefixLift 4149924
  have htrace : WordTrace (prefixWord ++ tailWord_4149924) baseStart_4149924 baseEnd_4149924 := by
    simpa [prefixWord, tailWord_4149924, baseEnd_4149924] using wordTrace_append hprefix tailTrace_4149924
  have hstable : (prefixWord ++ tailWord_4149924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149924).length < 2 ^ (prefixWord ++ tailWord_4149924).sum := by decide
  have hdescent : baseEnd_4149924 < baseStart_4149924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149941 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 3, 3, 2]
def baseStart_4149941 : Nat := 118140960795 + 4149941 * 2 ^ 59
def prefixEnd_4149941 : Nat := 4983230072969 + 3 ^ 40 * 4149941 * 2
def baseEnd_4149941 : Nat := 2130914420800253070452275

theorem tailTrace_4149941 : CollatzResearch.WordTrace tailWord_4149941 prefixEnd_4149941 2130914420800253070452275 := by
  unfold tailWord_4149941
  simp only [CollatzResearch.WordTrace]
  refine ⟨151360783058479985341161677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100907188705653323560774451 151360783058479985341161677)
  ·
    refine ⟨56760293646929994502935629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151360783058479985341161677 56760293646929994502935629)
    ·
      refine ⟨21285110117598747938600861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56760293646929994502935629 21285110117598747938600861)
      ·
        refine ⟨7981916294099530476975323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21285110117598747938600861 7981916294099530476975323)
        ·
          refine ⟨11972874441149295715462985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7981916294099530476975323 11972874441149295715462985)
          ·
            refine ⟨8979655830861971786597239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11972874441149295715462985 8979655830861971786597239)
            ·
              refine ⟨13469483746292957679895859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8979655830861971786597239 13469483746292957679895859)
              ·
                refine ⟨20204225619439436519843789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13469483746292957679895859 20204225619439436519843789)
                ·
                  refine ⟨7576584607289788694941421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20204225619439436519843789 7576584607289788694941421)
                  ·
                    refine ⟨2841219227733670760603033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7576584607289788694941421 2841219227733670760603033)
                    ·
                      refine ⟨2130914420800253070452275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841219227733670760603033 2130914420800253070452275)
                      ·
                        rfl

theorem cell23_4149941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_4149941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149941 prefixEnd_4149941 := by exact prefixLift 4149941
  have htrace : WordTrace (prefixWord ++ tailWord_4149941) baseStart_4149941 baseEnd_4149941 := by
    simpa [prefixWord, tailWord_4149941, baseEnd_4149941] using wordTrace_append hprefix tailTrace_4149941
  have hstable : (prefixWord ++ tailWord_4149941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149941).length < 2 ^ (prefixWord ++ tailWord_4149941).sum := by decide
  have hdescent : baseEnd_4149941 < baseStart_4149941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4149965 : List Nat := [1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_4149965 : Nat := 118140960795 + 4149965 * 2 ^ 59
def prefixEnd_4149965 : Nat := 4983230072969 + 3 ^ 40 * 4149965 * 2
def baseEnd_4149965 : Nat := 2130926744335960976552165

theorem tailTrace_4149965 : CollatzResearch.WordTrace tailWord_4149965 prefixEnd_4149965 2130926744335960976552165 := by
  unfold tailWord_4149965
  simp only [CollatzResearch.WordTrace]
  refine ⟨151361658410393037440035349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100907772273595358293356899 151361658410393037440035349)
  ·
    refine ⟨7095077737987173630001657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151361658410393037440035349 7095077737987173630001657)
    ·
      refine ⟨5321308303490380222501243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7095077737987173630001657 5321308303490380222501243)
      ·
        refine ⟨7981962455235570333751865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321308303490380222501243 7981962455235570333751865)
        ·
          refine ⟨5986471841426677750313899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7981962455235570333751865 5986471841426677750313899)
          ·
            refine ⟨8979707762140016625470849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986471841426677750313899 8979707762140016625470849)
            ·
              refine ⟨6734780821605012469103137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8979707762140016625470849 6734780821605012469103137)
              ·
                refine ⟨5051085616203759351827353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6734780821605012469103137 5051085616203759351827353)
                ·
                  refine ⟨3788314212152819513870515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5051085616203759351827353 3788314212152819513870515)
                  ·
                    refine ⟨5682471318229229270805773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3788314212152819513870515 5682471318229229270805773)
                    ·
                      refine ⟨2130926744335960976552165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5682471318229229270805773 2130926744335960976552165)
                      ·
                        rfl

theorem cell23_4149965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_4149965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4149965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4149965 prefixEnd_4149965 := by exact prefixLift 4149965
  have htrace : WordTrace (prefixWord ++ tailWord_4149965) baseStart_4149965 baseEnd_4149965 := by
    simpa [prefixWord, tailWord_4149965, baseEnd_4149965] using wordTrace_append hprefix tailTrace_4149965
  have hstable : (prefixWord ++ tailWord_4149965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4149965).length < 2 ^ (prefixWord ++ tailWord_4149965).sum := by decide
  have hdescent : baseEnd_4149965 < baseStart_4149965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4149965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150027 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 4]
def baseStart_4150027 : Nat := 118140960795 + 4150027 * 2 ^ 59
def prefixEnd_4150027 : Nat := 4983230072969 + 3 ^ 40 * 4150027 * 2
def baseEnd_4150027 : Nat := 2130958580136539733976879

theorem tailTrace_4150027 : CollatzResearch.WordTrace tailWord_4150027 prefixEnd_4150027 2130958580136539733976879 := by
  unfold tailWord_4150027
  simp only [CollatzResearch.WordTrace]
  refine ⟨151363919736168422028792335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100909279824112281352528223 151363919736168422028792335)
  ·
    refine ⟨227045879604252633043188503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151363919736168422028792335 227045879604252633043188503)
    ·
      refine ⟨340568819406378949564782755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227045879604252633043188503 340568819406378949564782755)
      ·
        refine ⟨510853229109568424347174133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340568819406378949564782755 510853229109568424347174133)
        ·
          refine ⟨47892490229022039782547575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510853229109568424347174133 47892490229022039782547575)
          ·
            refine ⟨71838735343533059673821363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47892490229022039782547575 71838735343533059673821363)
            ·
              refine ⟨107758103015299589510732045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71838735343533059673821363 107758103015299589510732045)
              ·
                refine ⟨40409288630737346066524517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107758103015299589510732045 40409288630737346066524517)
                ·
                  refine ⟨7576741618263252387473347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40409288630737346066524517 7576741618263252387473347)
                  ·
                    refine ⟨11365112427394878581210021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7576741618263252387473347 11365112427394878581210021)
                    ·
                      refine ⟨2130958580136539733976879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11365112427394878581210021 2130958580136539733976879)
                      ·
                        rfl

theorem cell23_4150027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 4].length) (baseStart_4150027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150027 prefixEnd_4150027 := by exact prefixLift 4150027
  have htrace : WordTrace (prefixWord ++ tailWord_4150027) baseStart_4150027 baseEnd_4150027 := by
    simpa [prefixWord, tailWord_4150027, baseEnd_4150027] using wordTrace_append hprefix tailTrace_4150027
  have hstable : (prefixWord ++ tailWord_4150027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150027).length < 2 ^ (prefixWord ++ tailWord_4150027).sum := by decide
  have hdescent : baseEnd_4150027 < baseStart_4150027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150067 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 8]
def baseStart_4150067 : Nat := 118140960795 + 4150067 * 2 ^ 59
def prefixEnd_4150067 : Nat := 4983230072969 + 3 ^ 40 * 4150067 * 2
def baseEnd_4150067 : Nat := 236775457706968841941855

theorem tailTrace_4150067 : CollatzResearch.WordTrace tailWord_4150067 prefixEnd_4150067 236775457706968841941855 := by
  unfold tailWord_4150067
  simp only [CollatzResearch.WordTrace]
  refine ⟨151365378656023508860248455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100910252437349005906832303 151365378656023508860248455)
  ·
    refine ⟨227048067984035263290372683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151365378656023508860248455 227048067984035263290372683)
    ·
      refine ⟨340572101976052894935559025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227048067984035263290372683 340572101976052894935559025)
      ·
        refine ⟨255429076482039671201669269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340572101976052894935559025 255429076482039671201669269)
        ·
          refine ⟨11973237960095609587578247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255429076482039671201669269 11973237960095609587578247)
          ·
            refine ⟨17959856940143414381367371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11973237960095609587578247 17959856940143414381367371)
            ·
              refine ⟨26939785410215121572051057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17959856940143414381367371 26939785410215121572051057)
              ·
                refine ⟨20204839057661341179038293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26939785410215121572051057 20204839057661341179038293)
                ·
                  refine ⟨236775457706968841941855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20204839057661341179038293 236775457706968841941855)
                  ·
                    rfl

theorem cell23_4150067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 8].length) (baseStart_4150067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150067 prefixEnd_4150067 := by exact prefixLift 4150067
  have htrace : WordTrace (prefixWord ++ tailWord_4150067) baseStart_4150067 baseEnd_4150067 := by
    simpa [prefixWord, tailWord_4150067, baseEnd_4150067] using wordTrace_append hprefix tailTrace_4150067
  have hstable : (prefixWord ++ tailWord_4150067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150067).length < 2 ^ (prefixWord ++ tailWord_4150067).sum := by decide
  have hdescent : baseEnd_4150067 < baseStart_4150067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150088 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 1, 4]
def baseStart_4150088 : Nat := 118140960795 + 4150088 * 2 ^ 59
def prefixEnd_4150088 : Nat := 4983230072969 + 3 ^ 40 * 4150088 * 2
def baseEnd_4150088 : Nat := 710329967485487998438033

theorem tailTrace_4150088 : CollatzResearch.WordTrace tailWord_4150088 prefixEnd_4150088 710329967485487998438033 := by
  unfold tailWord_4150088
  simp only [CollatzResearch.WordTrace]
  refine ⟨75683072294473714723381459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100910763059298286297841945 75683072294473714723381459)
  ·
    refine ⟨113524608441710572085072189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75683072294473714723381459 113524608441710572085072189)
    ·
      refine ⟨42571728165641464531902071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113524608441710572085072189 42571728165641464531902071)
      ·
        refine ⟨63857592248462196797853107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42571728165641464531902071 63857592248462196797853107)
        ·
          refine ⟨95786388372693295196779661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63857592248462196797853107 95786388372693295196779661)
          ·
            refine ⟨35919895639759985698792373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95786388372693295196779661 35919895639759985698792373)
            ·
              refine ⟨3367490216227498659261785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35919895639759985698792373 3367490216227498659261785)
              ·
                refine ⟨2525617662170623994446339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3367490216227498659261785 2525617662170623994446339)
                ·
                  refine ⟨3788426493255935991669509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525617662170623994446339 3788426493255935991669509)
                  ·
                    refine ⟨710329967485487998438033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3788426493255935991669509 710329967485487998438033)
                    ·
                      rfl

theorem cell23_4150088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_4150088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150088 prefixEnd_4150088 := by exact prefixLift 4150088
  have htrace : WordTrace (prefixWord ++ tailWord_4150088) baseStart_4150088 baseEnd_4150088 := by
    simpa [prefixWord, tailWord_4150088, baseEnd_4150088] using wordTrace_append hprefix tailTrace_4150088
  have hstable : (prefixWord ++ tailWord_4150088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150088).length < 2 ^ (prefixWord ++ tailWord_4150088).sum := by decide
  have hdescent : baseEnd_4150088 < baseStart_4150088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150104 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 3, 5, 2]
def baseStart_4150104 : Nat := 118140960795 + 4150104 * 2 ^ 59
def prefixEnd_4150104 : Nat := 4983230072969 + 3 ^ 40 * 4150104 * 2
def baseEnd_4150104 : Nat := 2130998118146935932714025

theorem tailTrace_4150104 : CollatzResearch.WordTrace tailWord_4150104 prefixEnd_4150104 2130998118146935932714025 := by
  unfold tailWord_4150104
  simp only [CollatzResearch.WordTrace]
  refine ⟨75683364078444732089672683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100911152104592976119563577 75683364078444732089672683)
  ·
    refine ⟨113525046117667098134509025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75683364078444732089672683 113525046117667098134509025)
    ·
      refine ⟨85143784588250323600881769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113525046117667098134509025 85143784588250323600881769)
      ·
        refine ⟨63857838441187742700661327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85143784588250323600881769 63857838441187742700661327)
        ·
          refine ⟨95786757661781614050991991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63857838441187742700661327 95786757661781614050991991)
          ·
            refine ⟨143680136492672421076487987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95786757661781614050991991 143680136492672421076487987)
            ·
              refine ⟨215520204739008631614731981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143680136492672421076487987 215520204739008631614731981)
              ·
                refine ⟨80820076777128236855524493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215520204739008631614731981 80820076777128236855524493)
                ·
                  refine ⟨30307528791423088820821685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80820076777128236855524493 30307528791423088820821685)
                  ·
                    refine ⟨2841330824195914576952033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30307528791423088820821685 2841330824195914576952033)
                    ·
                      refine ⟨2130998118146935932714025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841330824195914576952033 2130998118146935932714025)
                      ·
                        rfl

theorem cell23_4150104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_4150104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150104 prefixEnd_4150104 := by exact prefixLift 4150104
  have htrace : WordTrace (prefixWord ++ tailWord_4150104) baseStart_4150104 baseEnd_4150104 := by
    simpa [prefixWord, tailWord_4150104, baseEnd_4150104] using wordTrace_append hprefix tailTrace_4150104
  have hstable : (prefixWord ++ tailWord_4150104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150104).length < 2 ^ (prefixWord ++ tailWord_4150104).sum := by decide
  have hdescent : baseEnd_4150104 < baseStart_4150104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150172 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4150172 : Nat := 118140960795 + 4150172 * 2 ^ 59
def prefixEnd_4150172 : Nat := 4983230072969 + 3 ^ 40 * 4150172 * 2
def baseEnd_4150172 : Nat := 2131033034831441666663713

theorem tailTrace_4150172 : CollatzResearch.WordTrace tailWord_4150172 prefixEnd_4150172 2131033034831441666663713 := by
  unfold tailWord_4150172
  simp only [CollatzResearch.WordTrace]
  refine ⟨75684604160321555896410385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100912805547095407861880513 75684604160321555896410385)
  ·
    refine ⟨56763453120241166922307789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75684604160321555896410385 56763453120241166922307789)
    ·
      refine ⟨21286294920090437595865421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56763453120241166922307789 21286294920090437595865421)
      ·
        refine ⟨7982360595033914098449533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21286294920090437595865421 7982360595033914098449533)
        ·
          refine ⟨2993385223137717786918575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7982360595033914098449533 2993385223137717786918575)
          ·
            refine ⟨4490077834706576680377863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993385223137717786918575 4490077834706576680377863)
            ·
              refine ⟨6735116752059865020566795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490077834706576680377863 6735116752059865020566795)
              ·
                refine ⟨10102675128089797530850193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735116752059865020566795 10102675128089797530850193)
                ·
                  refine ⟨7577006346067348148137645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10102675128089797530850193 7577006346067348148137645)
                  ·
                    refine ⟨2841377379775255555551617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7577006346067348148137645 2841377379775255555551617)
                    ·
                      refine ⟨2131033034831441666663713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841377379775255555551617 2131033034831441666663713)
                      ·
                        rfl

theorem cell23_4150172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4150172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150172 prefixEnd_4150172 := by exact prefixLift 4150172
  have htrace : WordTrace (prefixWord ++ tailWord_4150172) baseStart_4150172 baseEnd_4150172 := by
    simpa [prefixWord, tailWord_4150172, baseEnd_4150172] using wordTrace_append hprefix tailTrace_4150172
  have hstable : (prefixWord ++ tailWord_4150172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150172).length < 2 ^ (prefixWord ++ tailWord_4150172).sum := by decide
  have hdescent : baseEnd_4150172 < baseStart_4150172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150185 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 1, 2, 2]
def baseStart_4150185 : Nat := 118140960795 + 4150185 * 2 ^ 59
def prefixEnd_4150185 : Nat := 4983230072969 + 3 ^ 40 * 4150185 * 2
def baseEnd_4150185 : Nat := 2131039710079950115801153

theorem tailTrace_4150185 : CollatzResearch.WordTrace tailWord_4150185 prefixEnd_4150185 2131039710079950115801153 := by
  unfold tailWord_4150185
  simp only [CollatzResearch.WordTrace]
  refine ⟨151369682469596015013044009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100913121646397343342029339 151369682469596015013044009)
  ·
    refine ⟨113527261852197011259783007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151369682469596015013044009 113527261852197011259783007)
    ·
      refine ⟨170290892778295516889674511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113527261852197011259783007 170290892778295516889674511)
      ·
        refine ⟨255436339167443275334511767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170290892778295516889674511 255436339167443275334511767)
        ·
          refine ⟨383154508751164913001767651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255436339167443275334511767 383154508751164913001767651)
          ·
            refine ⟨574731763126747369502651477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383154508751164913001767651 574731763126747369502651477)
            ·
              refine ⟨6735137849141570736359197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 574731763126747369502651477 6735137849141570736359197)
              ·
                refine ⟨2525676693428089026134699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6735137849141570736359197 2525676693428089026134699)
                ·
                  refine ⟨3788515040142133539202049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525676693428089026134699 3788515040142133539202049)
                  ·
                    refine ⟨2841386280106600154401537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3788515040142133539202049 2841386280106600154401537)
                    ·
                      refine ⟨2131039710079950115801153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841386280106600154401537 2131039710079950115801153)
                      ·
                        rfl

theorem cell23_4150185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 1, 2, 2].length) (baseStart_4150185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150185 prefixEnd_4150185 := by exact prefixLift 4150185
  have htrace : WordTrace (prefixWord ++ tailWord_4150185) baseStart_4150185 baseEnd_4150185 := by
    simpa [prefixWord, tailWord_4150185, baseEnd_4150185] using wordTrace_append hprefix tailTrace_4150185
  have hstable : (prefixWord ++ tailWord_4150185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150185).length < 2 ^ (prefixWord ++ tailWord_4150185).sum := by decide
  have hdescent : baseEnd_4150185 < baseStart_4150185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150187 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 4, 7]
def baseStart_4150187 : Nat := 118140960795 + 4150187 * 2 ^ 59
def prefixEnd_4150187 : Nat := 4983230072969 + 3 ^ 40 * 4150187 * 2
def baseEnd_4150187 : Nat := 710346912347086369325381

theorem tailTrace_4150187 : CollatzResearch.WordTrace tailWord_4150187 prefixEnd_4150187 710346912347086369325381 := by
  unfold tailWord_4150187
  simp only [CollatzResearch.WordTrace]
  refine ⟨151369755415588769354616815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100913170277059179569744543 151369755415588769354616815)
  ·
    refine ⟨227054633123383154031925223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151369755415588769354616815 227054633123383154031925223)
    ·
      refine ⟨340581949685074731047887835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227054633123383154031925223 340581949685074731047887835)
      ·
        refine ⟨510872924527612096571831753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340581949685074731047887835 510872924527612096571831753)
        ·
          refine ⟨383154693395709072428873815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510872924527612096571831753 383154693395709072428873815)
          ·
            refine ⟨574732040093563608643310723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383154693395709072428873815 574732040093563608643310723)
            ·
              refine ⟨862098060140345412964966085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574732040093563608643310723 862098060140345412964966085)
              ·
                refine ⟨161643386276314764930931141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 862098060140345412964966085 161643386276314764930931141)
                ·
                  refine ⟨30308134926809018424549589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161643386276314764930931141 30308134926809018424549589)
                  ·
                    refine ⟨710346912347086369325381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30308134926809018424549589 710346912347086369325381)
                    ·
                      rfl

theorem cell23_4150187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_4150187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150187 prefixEnd_4150187 := by exact prefixLift 4150187
  have htrace : WordTrace (prefixWord ++ tailWord_4150187) baseStart_4150187 baseEnd_4150187 := by
    simpa [prefixWord, tailWord_4150187, baseEnd_4150187] using wordTrace_append hprefix tailTrace_4150187
  have hstable : (prefixWord ++ tailWord_4150187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150187).length < 2 ^ (prefixWord ++ tailWord_4150187).sum := by decide
  have hdescent : baseEnd_4150187 < baseStart_4150187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150212 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 2, 4]
def baseStart_4150212 : Nat := 118140960795 + 4150212 * 2 ^ 59
def prefixEnd_4150212 : Nat := 4983230072969 + 3 ^ 40 * 4150212 * 2
def baseEnd_4150212 : Nat := 710351191352540503387843

theorem tailTrace_4150212 : CollatzResearch.WordTrace tailWord_4150212 prefixEnd_4150212 710351191352540503387843 := by
  unfold tailWord_4150212
  simp only [CollatzResearch.WordTrace]
  refine ⟨75685333620249099312138445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100913778160332132416184593 75685333620249099312138445)
  ·
    refine ⟨28382000107593412242051917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75685333620249099312138445 28382000107593412242051917)
    ·
      refine ⟨10643250040347529590769469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28382000107593412242051917 10643250040347529590769469)
      ·
        refine ⟨3991218765130323596538551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10643250040347529590769469 3991218765130323596538551)
        ·
          refine ⟨5986828147695485394807827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991218765130323596538551 5986828147695485394807827)
          ·
            refine ⟨8980242221543228092211741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5986828147695485394807827 8980242221543228092211741)
            ·
              refine ⟨3367590833078710534579403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8980242221543228092211741 3367590833078710534579403)
              ·
                refine ⟨5051386249618065801869105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3367590833078710534579403 5051386249618065801869105)
                ·
                  refine ⟨3788539687213549351401829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5051386249618065801869105 3788539687213549351401829)
                  ·
                    refine ⟨710351191352540503387843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3788539687213549351401829 710351191352540503387843)
                    ·
                      rfl

theorem cell23_4150212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_4150212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150212 prefixEnd_4150212 := by exact prefixLift 4150212
  have htrace : WordTrace (prefixWord ++ tailWord_4150212) baseStart_4150212 baseEnd_4150212 := by
    simpa [prefixWord, tailWord_4150212, baseEnd_4150212] using wordTrace_append hprefix tailTrace_4150212
  have hstable : (prefixWord ++ tailWord_4150212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150212).length < 2 ^ (prefixWord ++ tailWord_4150212).sum := by decide
  have hdescent : baseEnd_4150212 < baseStart_4150212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150241 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 3, 4, 2]
def baseStart_4150241 : Nat := 118140960795 + 4150241 * 2 ^ 59
def prefixEnd_4150241 : Nat := 4983230072969 + 3 ^ 40 * 4150241 * 2
def baseEnd_4150241 : Nat := 2131068464996601896700895

theorem tailTrace_4150241 : CollatzResearch.WordTrace tailWord_4150241 prefixEnd_4150241 2131068464996601896700895 := by
  unfold tailWord_4150241
  simp only [CollatzResearch.WordTrace]
  refine ⟨151371724957393136577082577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100914483304928757718055051 151371724957393136577082577)
  ·
    refine ⟨113528793718044852432811933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151371724957393136577082577 113528793718044852432811933)
    ·
      refine ⟨42573297644266819662304475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113528793718044852432811933 42573297644266819662304475)
      ·
        refine ⟨63859946466400229493456713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42573297644266819662304475 63859946466400229493456713)
        ·
          refine ⟨47894959849800172120092535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63859946466400229493456713 47894959849800172120092535)
          ·
            refine ⟨71842439774700258180138803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47894959849800172120092535 71842439774700258180138803)
            ·
              refine ⟨107763659662050387270208205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71842439774700258180138803 107763659662050387270208205)
              ·
                refine ⟨40411372373268895226328077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107763659662050387270208205 40411372373268895226328077)
                ·
                  refine ⟨15154264639975835709873029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40411372373268895226328077 15154264639975835709873029)
                  ·
                    refine ⟨2841424619995469195601193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15154264639975835709873029 2841424619995469195601193)
                    ·
                      refine ⟨2131068464996601896700895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841424619995469195601193 2131068464996601896700895)
                      ·
                        rfl

theorem cell23_4150241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_4150241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150241 prefixEnd_4150241 := by exact prefixLift 4150241
  have htrace : WordTrace (prefixWord ++ tailWord_4150241) baseStart_4150241 baseEnd_4150241 := by
    simpa [prefixWord, tailWord_4150241, baseEnd_4150241] using wordTrace_append hprefix tailTrace_4150241
  have hstable : (prefixWord ++ tailWord_4150241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150241).length < 2 ^ (prefixWord ++ tailWord_4150241).sum := by decide
  have hdescent : baseEnd_4150241 < baseStart_4150241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150318 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_4150318 : Nat := 118140960795 + 4150318 * 2 ^ 59
def prefixEnd_4150318 : Nat := 4983230072969 + 3 ^ 40 * 4150318 * 2
def baseEnd_4150318 : Nat := 2131108003006998095438041

theorem tailTrace_4150318 : CollatzResearch.WordTrace tailWord_4150318 prefixEnd_4150318 2131108003006998095438041 := by
  unfold tailWord_4150318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18921816672264272340954451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100916355585409452485090405 18921816672264272340954451)
  ·
    refine ⟨28382725008396408511431677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18921816672264272340954451 28382725008396408511431677)
    ·
      refine ⟨10643521878148653191786879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28382725008396408511431677 10643521878148653191786879)
      ·
        refine ⟨15965282817222979787680319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643521878148653191786879 15965282817222979787680319)
        ·
          refine ⟨23947924225834469681520479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15965282817222979787680319 23947924225834469681520479)
          ·
            refine ⟨35921886338751704522280719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23947924225834469681520479 35921886338751704522280719)
            ·
              refine ⟨53882829508127556783421079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35921886338751704522280719 53882829508127556783421079)
              ·
                refine ⟨80824244262191335175131619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53882829508127556783421079 80824244262191335175131619)
                ·
                  refine ⟨121236366393287002762697429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80824244262191335175131619 121236366393287002762697429)
                  ·
                    refine ⟨2841477337342664127250721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 121236366393287002762697429 2841477337342664127250721)
                    ·
                      refine ⟨2131108003006998095438041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841477337342664127250721 2131108003006998095438041)
                      ·
                        rfl

theorem cell23_4150318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_4150318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150318 prefixEnd_4150318 := by exact prefixLift 4150318
  have htrace : WordTrace (prefixWord ++ tailWord_4150318) baseStart_4150318 baseEnd_4150318 := by
    simpa [prefixWord, tailWord_4150318, baseEnd_4150318] using wordTrace_append hprefix tailTrace_4150318
  have hstable : (prefixWord ++ tailWord_4150318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150318).length < 2 ^ (prefixWord ++ tailWord_4150318).sum := by decide
  have hdescent : baseEnd_4150318 < baseStart_4150318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150341 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_4150341 : Nat := 118140960795 + 4150341 * 2 ^ 59
def prefixEnd_4150341 : Nat := 4983230072969 + 3 ^ 40 * 4150341 * 2
def baseEnd_4150341 : Nat := 710373271020683835150145

theorem tailTrace_4150341 : CollatzResearch.WordTrace tailWord_4150341 prefixEnd_4150341 710373271020683835150145 := by
  unfold tailWord_4150341
  simp only [CollatzResearch.WordTrace]
  refine ⟨151375372257030853655722877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100916914838020569103815251 151375372257030853655722877)
  ·
    refine ⟨56765764596386570120896079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151375372257030853655722877 56765764596386570120896079)
    ·
      refine ⟨85148646894579855181344119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56765764596386570120896079 85148646894579855181344119)
      ·
        refine ⟨127722970341869782772016179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85148646894579855181344119 127722970341869782772016179)
        ·
          refine ⟨191584455512804674158024269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127722970341869782772016179 191584455512804674158024269)
          ·
            refine ⟨71844170817301752809259101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191584455512804674158024269 71844170817301752809259101)
            ·
              refine ⟨26941564056488157303472163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71844170817301752809259101 26941564056488157303472163)
              ·
                refine ⟨40412346084732235955208245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26941564056488157303472163 40412346084732235955208245)
                ·
                  refine ⟨3788657445443647120800773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40412346084732235955208245 3788657445443647120800773)
                  ·
                    refine ⟨710373271020683835150145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3788657445443647120800773 710373271020683835150145)
                    ·
                      rfl

theorem cell23_4150341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_4150341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150341 prefixEnd_4150341 := by exact prefixLift 4150341
  have htrace : WordTrace (prefixWord ++ tailWord_4150341) baseStart_4150341 baseEnd_4150341 := by
    simpa [prefixWord, tailWord_4150341, baseEnd_4150341] using wordTrace_append hprefix tailTrace_4150341
  have hstable : (prefixWord ++ tailWord_4150341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150341).length < 2 ^ (prefixWord ++ tailWord_4150341).sum := by decide
  have hdescent : baseEnd_4150341 < baseStart_4150341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150375 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 1, 4]
def baseStart_4150375 : Nat := 118140960795 + 4150375 * 2 ^ 59
def prefixEnd_4150375 : Nat := 4983230072969 + 3 ^ 40 * 4150375 * 2
def baseEnd_4150375 : Nat := 710379090468101457475093

theorem tailTrace_4150375 : CollatzResearch.WordTrace tailWord_4150375 prefixEnd_4150375 710379090468101457475093 := by
  unfold tailWord_4150375
  simp only [CollatzResearch.WordTrace]
  refine ⟨151376612338907677462460579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100917741559271784974973719 151376612338907677462460579)
  ·
    refine ⟨227064918508361516193690869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151376612338907677462460579 227064918508361516193690869)
    ·
      refine ⟨21287336110158892143158519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 227064918508361516193690869 21287336110158892143158519)
      ·
        refine ⟨31931004165238338214737779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21287336110158892143158519 31931004165238338214737779)
        ·
          refine ⟨47896506247857507322106669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31931004165238338214737779 47896506247857507322106669)
          ·
            refine ⟨17961189842946565245790001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47896506247857507322106669 17961189842946565245790001)
            ·
              refine ⟨13470892382209923934342501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17961189842946565245790001 13470892382209923934342501)
              ·
                refine ⟨2525792321664360737689219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13470892382209923934342501 2525792321664360737689219)
                ·
                  refine ⟨3788688482496541106533829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525792321664360737689219 3788688482496541106533829)
                  ·
                    refine ⟨710379090468101457475093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3788688482496541106533829 710379090468101457475093)
                    ·
                      rfl

theorem cell23_4150375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_4150375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150375 prefixEnd_4150375 := by exact prefixLift 4150375
  have htrace : WordTrace (prefixWord ++ tailWord_4150375) baseStart_4150375 baseEnd_4150375 := by
    simpa [prefixWord, tailWord_4150375, baseEnd_4150375] using wordTrace_append hprefix tailTrace_4150375
  have hstable : (prefixWord ++ tailWord_4150375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150375).length < 2 ^ (prefixWord ++ tailWord_4150375).sum := by decide
  have hdescent : baseEnd_4150375 < baseStart_4150375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150448 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 2, 4]
def baseStart_4150448 : Nat := 118140960795 + 4150448 * 2 ^ 59
def prefixEnd_4150448 : Nat := 4983230072969 + 3 ^ 40 * 4150448 * 2
def baseEnd_4150448 : Nat := 710391585164027528937481

theorem tailTrace_4150448 : CollatzResearch.WordTrace tailWord_4150448 prefixEnd_4150448 710391585164027528937481 := by
  unfold tailWord_4150448
  simp only [CollatzResearch.WordTrace]
  refine ⟨75689637433821605464933999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100919516578428807286578665 75689637433821605464933999)
  ·
    refine ⟨113534456150732408197400999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75689637433821605464933999 113534456150732408197400999)
    ·
      refine ⟨170301684226098612296101499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113534456150732408197400999 170301684226098612296101499)
      ·
        refine ⟨255452526339147918444152249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170301684226098612296101499 255452526339147918444152249)
        ·
          refine ⟨191589394754360938833114187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255452526339147918444152249 191589394754360938833114187)
          ·
            refine ⟨287384092131541408249671281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191589394754360938833114187 287384092131541408249671281)
            ·
              refine ⟨215538069098656056187253461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287384092131541408249671281 215538069098656056187253461)
              ·
                refine ⟨5051673494499751316888753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 215538069098656056187253461 5051673494499751316888753)
                ·
                  refine ⟨3788755120874813487666565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5051673494499751316888753 3788755120874813487666565)
                  ·
                    refine ⟨710391585164027528937481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3788755120874813487666565 710391585164027528937481)
                    ·
                      rfl

theorem cell23_4150448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 4].length) (baseStart_4150448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150448 prefixEnd_4150448 := by exact prefixLift 4150448
  have htrace : WordTrace (prefixWord ++ tailWord_4150448) baseStart_4150448 baseEnd_4150448 := by
    simpa [prefixWord, tailWord_4150448, baseEnd_4150448] using wordTrace_append hprefix tailTrace_4150448
  have hstable : (prefixWord ++ tailWord_4150448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150448).length < 2 ^ (prefixWord ++ tailWord_4150448).sum := by decide
  have hdescent : baseEnd_4150448 < baseStart_4150448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150451 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6]
def baseStart_4150451 : Nat := 118140960795 + 4150451 * 2 ^ 59
def prefixEnd_4150451 : Nat := 4983230072969 + 3 ^ 40 * 4150451 * 2
def baseEnd_4150451 : Nat := 2131176295934046075074929

theorem tailTrace_4150451 : CollatzResearch.WordTrace tailWord_4150451 prefixEnd_4150451 2131176295934046075074929 := by
  unfold tailWord_4150451
  simp only [CollatzResearch.WordTrace]
  refine ⟨151379384286632342442227207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100919589524421561628151471 151379384286632342442227207)
  ·
    refine ⟨227069076429948513663340811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151379384286632342442227207 227069076429948513663340811)
    ·
      refine ⟨340603614644922770495011217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227069076429948513663340811 340603614644922770495011217)
      ·
        refine ⟨255452710983692077871258413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340603614644922770495011217 255452710983692077871258413)
        ·
          refine ⟨95794766618884529201721905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255452710983692077871258413 95794766618884529201721905)
          ·
            refine ⟨71846074964163396901291429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95794766618884529201721905 71846074964163396901291429)
            ·
              refine ⟨13471139055780636918992143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71846074964163396901291429 13471139055780636918992143)
              ·
                refine ⟨20206708583670955378488215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471139055780636918992143 20206708583670955378488215)
                ·
                  refine ⟨30310062875506433067732323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20206708583670955378488215 30310062875506433067732323)
                  ·
                    refine ⟨45465094313259649601598485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30310062875506433067732323 45465094313259649601598485)
                    ·
                      refine ⟨2131176295934046075074929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45465094313259649601598485 2131176295934046075074929)
                      ·
                        rfl

theorem cell23_4150451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_4150451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150451 prefixEnd_4150451 := by exact prefixLift 4150451
  have htrace : WordTrace (prefixWord ++ tailWord_4150451) baseStart_4150451 baseEnd_4150451 := by
    simpa [prefixWord, tailWord_4150451, baseEnd_4150451] using wordTrace_append hprefix tailTrace_4150451
  have hstable : (prefixWord ++ tailWord_4150451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150451).length < 2 ^ (prefixWord ++ tailWord_4150451).sum := by decide
  have hdescent : baseEnd_4150451 < baseStart_4150451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150455 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 5, 2, 2]
def baseStart_4150455 : Nat := 118140960795 + 4150455 * 2 ^ 59
def prefixEnd_4150455 : Nat := 4983230072969 + 3 ^ 40 * 4150455 * 2
def baseEnd_4150455 : Nat := 2131178349856664059424911

theorem tailTrace_4150455 : CollatzResearch.WordTrace tailWord_4150455 prefixEnd_4150455 2131178349856664059424911 := by
  unfold tailWord_4150455
  simp only [CollatzResearch.WordTrace]
  refine ⟨151379530178617851125372819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100919686785745234083581879 151379530178617851125372819)
  ·
    refine ⟨227069295267926776688059229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151379530178617851125372819 227069295267926776688059229)
    ·
      refine ⟨85150985725472541258022211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227069295267926776688059229 85150985725472541258022211)
      ·
        refine ⟨127726478588208811887033317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85150985725472541258022211 127726478588208811887033317)
        ·
          refine ⟨23948714735289152228818747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127726478588208811887033317 23948714735289152228818747)
          ·
            refine ⟨35923072102933728343228121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23948714735289152228818747 35923072102933728343228121)
            ·
              refine ⟨26942304077200296257421091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35923072102933728343228121 26942304077200296257421091)
              ·
                refine ⟨40413456115800444386131637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26942304077200296257421091 40413456115800444386131637)
                ·
                  refine ⟨3788761510856291661199841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40413456115800444386131637 3788761510856291661199841)
                  ·
                    refine ⟨2841571133142218745899881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3788761510856291661199841 2841571133142218745899881)
                    ·
                      refine ⟨2131178349856664059424911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841571133142218745899881 2131178349856664059424911)
                      ·
                        rfl

theorem cell23_4150455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_4150455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150455 prefixEnd_4150455 := by exact prefixLift 4150455
  have htrace : WordTrace (prefixWord ++ tailWord_4150455) baseStart_4150455 baseEnd_4150455 := by
    simpa [prefixWord, tailWord_4150455, baseEnd_4150455] using wordTrace_append hprefix tailTrace_4150455
  have hstable : (prefixWord ++ tailWord_4150455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150455).length < 2 ^ (prefixWord ++ tailWord_4150455).sum := by decide
  have hdescent : baseEnd_4150455 < baseStart_4150455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150461 : List Nat := [1, 4, 1, 2, 1, 1, 4, 9]
def baseStart_4150461 : Nat := 118140960795 + 4150461 * 2 ^ 59
def prefixEnd_4150461 : Nat := 4983230072969 + 3 ^ 40 * 4150461 * 2
def baseEnd_4150461 : Nat := 78932645582984853183329

theorem tailTrace_4150461 : CollatzResearch.WordTrace tailWord_4150461 prefixEnd_4150461 78932645582984853183329 := by
  unfold tailWord_4150461
  simp only [CollatzResearch.WordTrace]
  refine ⟨151379749016596114150091237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100919832677730742766727491 151379749016596114150091237)
  ·
    refine ⟨28383702940611771403142107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151379749016596114150091237 28383702940611771403142107)
    ·
      refine ⟨42575554410917657104713161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28383702940611771403142107 42575554410917657104713161)
      ·
        refine ⟨31931665808188242828534871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42575554410917657104713161 31931665808188242828534871)
        ·
          refine ⟨47897498712282364242802307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31931665808188242828534871 47897498712282364242802307)
          ·
            refine ⟨71846248068423546364203461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47897498712282364242802307 71846248068423546364203461)
            ·
              refine ⟨13471171512829414943288149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71846248068423546364203461 13471171512829414943288149)
              ·
                refine ⟨78932645582984853183329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13471171512829414943288149 78932645582984853183329)
                ·
                  rfl

theorem cell23_4150461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 9].length) (baseStart_4150461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150461 prefixEnd_4150461 := by exact prefixLift 4150461
  have htrace : WordTrace (prefixWord ++ tailWord_4150461) baseStart_4150461 baseEnd_4150461 := by
    simpa [prefixWord, tailWord_4150461, baseEnd_4150461] using wordTrace_append hprefix tailTrace_4150461
  have hstable : (prefixWord ++ tailWord_4150461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150461).length < 2 ^ (prefixWord ++ tailWord_4150461).sum := by decide
  have hdescent : baseEnd_4150461 < baseStart_4150461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150465 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 1, 6]
def baseStart_4150465 : Nat := 118140960795 + 4150465 * 2 ^ 59
def prefixEnd_4150465 : Nat := 4983230072969 + 3 ^ 40 * 4150465 * 2
def baseEnd_4150465 : Nat := 710394494887736340099955

theorem tailTrace_4150465 : CollatzResearch.WordTrace tailWord_4150465 prefixEnd_4150465 710394494887736340099955 := by
  unfold tailWord_4150465
  simp only [CollatzResearch.WordTrace]
  refine ⟨151379894908581622833236849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100919929939054415222157899 151379894908581622833236849)
  ·
    refine ⟨113534921181436217124927637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151379894908581622833236849 113534921181436217124927637)
    ·
      refine ⟨5321949430379822677730983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113534921181436217124927637 5321949430379822677730983)
      ·
        refine ⟨7982924145569734016596475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321949430379822677730983 7982924145569734016596475)
        ·
          refine ⟨11974386218354601024894713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7982924145569734016596475 11974386218354601024894713)
          ·
            refine ⟨8980789663765950768671035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11974386218354601024894713 8980789663765950768671035)
            ·
              refine ⟨13471184495648926153006553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8980789663765950768671035 13471184495648926153006553)
              ·
                refine ⟨10103388371736694614754915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13471184495648926153006553 10103388371736694614754915)
                ·
                  refine ⟨15155082557605041922132373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10103388371736694614754915 15155082557605041922132373)
                  ·
                    refine ⟨710394494887736340099955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15155082557605041922132373 710394494887736340099955)
                    ·
                      rfl

theorem cell23_4150465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_4150465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150465 prefixEnd_4150465 := by exact prefixLift 4150465
  have htrace : WordTrace (prefixWord ++ tailWord_4150465) baseStart_4150465 baseEnd_4150465 := by
    simpa [prefixWord, tailWord_4150465, baseEnd_4150465] using wordTrace_append hprefix tailTrace_4150465
  have hstable : (prefixWord ++ tailWord_4150465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150465).length < 2 ^ (prefixWord ++ tailWord_4150465).sum := by decide
  have hdescent : baseEnd_4150465 < baseStart_4150465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150478 : List Nat := [4, 1, 1, 1, 6, 10]
def baseStart_4150478 : Nat := 118140960795 + 4150478 * 2 ^ 59
def prefixEnd_4150478 : Nat := 4983230072969 + 3 ^ 40 * 4150478 * 2
def baseEnd_4150478 : Nat := 8770329876179907281635

theorem tailTrace_4150478 : CollatzResearch.WordTrace tailWord_4150478 prefixEnd_4150478 8770329876179907281635 := by
  unfold tailWord_4150478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18922546132191815756682511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100920246038356350702306725 18922546132191815756682511)
  ·
    refine ⟨28383819198287723635023767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18922546132191815756682511 28383819198287723635023767)
    ·
      refine ⟨42575728797431585452535651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28383819198287723635023767 42575728797431585452535651)
      ·
        refine ⟨63863593196147378178803477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42575728797431585452535651 63863593196147378178803477)
        ·
          refine ⟨2993605931069408352131413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63863593196147378178803477 2993605931069408352131413)
          ·
            refine ⟨8770329876179907281635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2993605931069408352131413 8770329876179907281635)
            ·
              rfl

theorem cell23_4150478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 10].length) (baseStart_4150478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150478 prefixEnd_4150478 := by exact prefixLift 4150478
  have htrace : WordTrace (prefixWord ++ tailWord_4150478) baseStart_4150478 baseEnd_4150478 := by
    simpa [prefixWord, tailWord_4150478, baseEnd_4150478] using wordTrace_append hprefix tailTrace_4150478
  have hstable : (prefixWord ++ tailWord_4150478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150478).length < 2 ^ (prefixWord ++ tailWord_4150478).sum := by decide
  have hdescent : baseEnd_4150478 < baseStart_4150478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150515 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 3, 3, 2]
def baseStart_4150515 : Nat := 118140960795 + 4150515 * 2 ^ 59
def prefixEnd_4150515 : Nat := 4983230072969 + 3 ^ 40 * 4150515 * 2
def baseEnd_4150515 : Nat := 2131209158695933824674635

theorem tailTrace_4150515 : CollatzResearch.WordTrace tailWord_4150515 prefixEnd_4150515 2131209158695933824674635 := by
  unfold tailWord_4150515
  simp only [CollatzResearch.WordTrace]
  refine ⟨151381718558400481372556999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100921145705600320915037999 151381718558400481372556999)
  ·
    refine ⟨227072577837600722058835499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151381718558400481372556999 227072577837600722058835499)
    ·
      refine ⟨340608866756401083088253249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227072577837600722058835499 340608866756401083088253249)
      ·
        refine ⟨255456650067300812316189937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340608866756401083088253249 255456650067300812316189937)
        ·
          refine ⟨191592487550475609237142453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255456650067300812316189937 191592487550475609237142453)
          ·
            refine ⟨17961795707857088365982105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 191592487550475609237142453 17961795707857088365982105)
            ·
              refine ⟨13471346780892816274486579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17961795707857088365982105 13471346780892816274486579)
              ·
                refine ⟨20207020171339224411729869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471346780892816274486579 20207020171339224411729869)
                ·
                  refine ⟨7577632564252209154398701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20207020171339224411729869 7577632564252209154398701)
                  ·
                    refine ⟨2841612211594578432899513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7577632564252209154398701 2841612211594578432899513)
                    ·
                      refine ⟨2131209158695933824674635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841612211594578432899513 2131209158695933824674635)
                      ·
                        rfl

theorem cell23_4150515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3, 2].length) (baseStart_4150515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150515 prefixEnd_4150515 := by exact prefixLift 4150515
  have htrace : WordTrace (prefixWord ++ tailWord_4150515) baseStart_4150515 baseEnd_4150515 := by
    simpa [prefixWord, tailWord_4150515, baseEnd_4150515] using wordTrace_append hprefix tailTrace_4150515
  have hstable : (prefixWord ++ tailWord_4150515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150515).length < 2 ^ (prefixWord ++ tailWord_4150515).sum := by decide
  have hdescent : baseEnd_4150515 < baseStart_4150515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150518 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4150518 : Nat := 118140960795 + 4150518 * 2 ^ 59
def prefixEnd_4150518 : Nat := 4983230072969 + 3 ^ 40 * 4150518 * 2
def baseEnd_4150518 : Nat := 2131210699137897312937121

theorem tailTrace_4150518 : CollatzResearch.WordTrace tailWord_4150518 prefixEnd_4150518 2131210699137897312937121 := by
  unfold tailWord_4150518
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461364248586850805307263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 100921218651593075256610805 9461364248586850805307263)
  ·
    refine ⟨14192046372880276207960895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9461364248586850805307263 14192046372880276207960895)
    ·
      refine ⟨21288069559320414311941343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14192046372880276207960895 21288069559320414311941343)
      ·
        refine ⟨31932104338980621467912015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21288069559320414311941343 31932104338980621467912015)
        ·
          refine ⟨47898156508470932201868023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31932104338980621467912015 47898156508470932201868023)
          ·
            refine ⟨71847234762706398302802035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47898156508470932201868023 71847234762706398302802035)
            ·
              refine ⟨107770852144059597454203053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71847234762706398302802035 107770852144059597454203053)
              ·
                refine ⟨40414069554022349045326145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107770852144059597454203053 40414069554022349045326145)
                ·
                  refine ⟨30310552165516761783994609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40414069554022349045326145 30310552165516761783994609)
                  ·
                    refine ⟨22732914124137571337995957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30310552165516761783994609 22732914124137571337995957)
                    ·
                      refine ⟨2131210699137897312937121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22732914124137571337995957 2131210699137897312937121)
                      ·
                        rfl

theorem cell23_4150518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4150518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150518 prefixEnd_4150518 := by exact prefixLift 4150518
  have htrace : WordTrace (prefixWord ++ tailWord_4150518) baseStart_4150518 baseEnd_4150518 := by
    simpa [prefixWord, tailWord_4150518, baseEnd_4150518] using wordTrace_append hprefix tailTrace_4150518
  have hstable : (prefixWord ++ tailWord_4150518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150518).length < 2 ^ (prefixWord ++ tailWord_4150518).sum := by decide
  have hdescent : baseEnd_4150518 < baseStart_4150518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150521 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 8]
def baseStart_4150521 : Nat := 118140960795 + 4150521 * 2 ^ 59
def prefixEnd_4150521 : Nat := 4983230072969 + 3 ^ 40 * 4150521 * 2
def baseEnd_4150521 : Nat := 710404079859953600399869

theorem tailTrace_4150521 : CollatzResearch.WordTrace tailWord_4150521 prefixEnd_4150521 710404079859953600399869 := by
  unfold tailWord_4150521
  simp only [CollatzResearch.WordTrace]
  refine ⟨151381937396378744397275417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100921291597585829598183611 151381937396378744397275417)
  ·
    refine ⟨113536453047284058297956563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151381937396378744397275417 113536453047284058297956563)
    ·
      refine ⟨170304679570926087446934845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113536453047284058297956563 170304679570926087446934845)
      ·
        refine ⟨63864254839097282792600567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170304679570926087446934845 63864254839097282792600567)
        ·
          refine ⟨95796382258645924188900851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63864254839097282792600567 95796382258645924188900851)
          ·
            refine ⟨143694573387968886283351277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95796382258645924188900851 143694573387968886283351277)
            ·
              refine ⟨53885465020488332356256729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143694573387968886283351277 53885465020488332356256729)
              ·
                refine ⟨40414098765366249267192547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53885465020488332356256729 40414098765366249267192547)
                ·
                  refine ⟨60621148148049373900788821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40414098765366249267192547 60621148148049373900788821)
                  ·
                    refine ⟨710404079859953600399869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 60621148148049373900788821 710404079859953600399869)
                    ·
                      rfl

theorem cell23_4150521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_4150521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150521 prefixEnd_4150521 := by exact prefixLift 4150521
  have htrace : WordTrace (prefixWord ++ tailWord_4150521) baseStart_4150521 baseEnd_4150521 := by
    simpa [prefixWord, tailWord_4150521, baseEnd_4150521] using wordTrace_append hprefix tailTrace_4150521
  have hstable : (prefixWord ++ tailWord_4150521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150521).length < 2 ^ (prefixWord ++ tailWord_4150521).sum := by decide
  have hdescent : baseEnd_4150521 < baseStart_4150521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150571 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_4150571 : Nat := 118140960795 + 4150571 * 2 ^ 59
def prefixEnd_4150571 : Nat := 4983230072969 + 3 ^ 40 * 4150571 * 2
def baseEnd_4150571 : Nat := 2131237913612585605574377

theorem tailTrace_4150571 : CollatzResearch.WordTrace tailWord_4150571 prefixEnd_4150571 2131237913612585605574377 := by
  unfold tailWord_4150571
  simp only [CollatzResearch.WordTrace]
  refine ⟨151383761046197602936595567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100922507364131735291063711 151383761046197602936595567)
  ·
    refine ⟨227075641569296404404893351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151383761046197602936595567 227075641569296404404893351)
    ·
      refine ⟨340613462353944606607340027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227075641569296404404893351 340613462353944606607340027)
      ·
        refine ⟨510920193530916909911010041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340613462353944606607340027 510920193530916909911010041)
        ·
          refine ⟨383190145148187682433257531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510920193530916909911010041 383190145148187682433257531)
          ·
            refine ⟨574785217722281523649886297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383190145148187682433257531 574785217722281523649886297)
            ·
              refine ⟨431088913291711142737414723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574785217722281523649886297 431088913291711142737414723)
              ·
                refine ⟨646633369937566714106122085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431088913291711142737414723 646633369937566714106122085)
                ·
                  refine ⟨121243756863293758894897891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646633369937566714106122085 121243756863293758894897891)
                  ·
                    refine ⟨181865635294940638342346837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121243756863293758894897891 181865635294940638342346837)
                    ·
                      refine ⟨2131237913612585605574377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 181865635294940638342346837 2131237913612585605574377)
                      ·
                        rfl

theorem cell23_4150571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_4150571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150571 prefixEnd_4150571 := by exact prefixLift 4150571
  have htrace : WordTrace (prefixWord ++ tailWord_4150571) baseStart_4150571 baseEnd_4150571 := by
    simpa [prefixWord, tailWord_4150571, baseEnd_4150571] using wordTrace_append hprefix tailTrace_4150571
  have hstable : (prefixWord ++ tailWord_4150571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150571).length < 2 ^ (prefixWord ++ tailWord_4150571).sum := by decide
  have hdescent : baseEnd_4150571 < baseStart_4150571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150608 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5]
def baseStart_4150608 : Nat := 118140960795 + 4150608 * 2 ^ 59
def prefixEnd_4150608 : Nat := 4983230072969 + 3 ^ 40 * 4150608 * 2
def baseEnd_4150608 : Nat := 2131256912396801960811707

theorem tailTrace_4150608 : CollatzResearch.WordTrace tailWord_4150608 prefixEnd_4150608 2131256912396801960811707 := by
  unfold tailWord_4150608
  simp only [CollatzResearch.WordTrace]
  refine ⟨75692555273531779127846239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100923407031375705503794985 75692555273531779127846239)
  ·
    refine ⟨113538832910297668691769359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75692555273531779127846239 113538832910297668691769359)
    ·
      refine ⟨170308249365446503037654039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113538832910297668691769359 170308249365446503037654039)
      ·
        refine ⟨255462374048169754556481059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170308249365446503037654039 255462374048169754556481059)
        ·
          refine ⟨383193561072254631834721589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255462374048169754556481059 383193561072254631834721589)
          ·
            refine ⟨35924396350523871734505149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 383193561072254631834721589 35924396350523871734505149)
            ·
              refine ⟨13471648631446451900439431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35924396350523871734505149 13471648631446451900439431)
              ·
                refine ⟨20207472947169677850659147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13471648631446451900439431 20207472947169677850659147)
                ·
                  refine ⟨30311209420754516775988721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20207472947169677850659147 30311209420754516775988721)
                  ·
                    refine ⟨22733407065565887581991541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30311209420754516775988721 22733407065565887581991541)
                    ·
                      refine ⟨2131256912396801960811707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22733407065565887581991541 2131256912396801960811707)
                      ·
                        rfl

theorem cell23_4150608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_4150608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150608 prefixEnd_4150608 := by exact prefixLift 4150608
  have htrace : WordTrace (prefixWord ++ tailWord_4150608) baseStart_4150608 baseEnd_4150608 := by
    simpa [prefixWord, tailWord_4150608, baseEnd_4150608] using wordTrace_append hprefix tailTrace_4150608
  have hstable : (prefixWord ++ tailWord_4150608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150608).length < 2 ^ (prefixWord ++ tailWord_4150608).sum := by decide
  have hdescent : baseEnd_4150608 < baseStart_4150608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150618 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_4150618 : Nat := 118140960795 + 4150618 * 2 ^ 59
def prefixEnd_4150618 : Nat := 4983230072969 + 3 ^ 40 * 4150618 * 2
def baseEnd_4150618 : Nat := 2131262047203346921686661

theorem tailTrace_4150618 : CollatzResearch.WordTrace tailWord_4150618 prefixEnd_4150618 2131262047203346921686661 := by
  unfold tailWord_4150618
  simp only [CollatzResearch.WordTrace]
  refine ⟨37846368819256832490889127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100923650184684886642371005 37846368819256832490889127)
  ·
    refine ⟨56769553228885248736333691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37846368819256832490889127 56769553228885248736333691)
    ·
      refine ⟨85154329843327873104500537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56769553228885248736333691 85154329843327873104500537)
      ·
        refine ⟨63865747382495904828375403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85154329843327873104500537 63865747382495904828375403)
        ·
          refine ⟨95798621073743857242563105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63865747382495904828375403 95798621073743857242563105)
          ·
            refine ⟨71848965805307892931922329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95798621073743857242563105 71848965805307892931922329)
            ·
              refine ⟨53886724353980919698941747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71848965805307892931922329 53886724353980919698941747)
              ·
                refine ⟨80830086530971379548412621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53886724353980919698941747 80830086530971379548412621)
                ·
                  refine ⟨30311282449114267330654733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80830086530971379548412621 30311282449114267330654733)
                  ·
                    refine ⟨11366730918417850248995525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30311282449114267330654733 11366730918417850248995525)
                    ·
                      refine ⟨2131262047203346921686661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11366730918417850248995525 2131262047203346921686661)
                      ·
                        rfl

theorem cell23_4150618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_4150618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150618 prefixEnd_4150618 := by exact prefixLift 4150618
  have htrace : WordTrace (prefixWord ++ tailWord_4150618) baseStart_4150618 baseEnd_4150618 := by
    simpa [prefixWord, tailWord_4150618, baseEnd_4150618] using wordTrace_append hprefix tailTrace_4150618
  have hstable : (prefixWord ++ tailWord_4150618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150618).length < 2 ^ (prefixWord ++ tailWord_4150618).sum := by decide
  have hdescent : baseEnd_4150618 < baseStart_4150618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150632 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 2, 5]
def baseStart_4150632 : Nat := 118140960795 + 4150632 * 2 ^ 59
def prefixEnd_4150632 : Nat := 4983230072969 + 3 ^ 40 * 4150632 * 2
def baseEnd_4150632 : Nat := 710423078644169955637199

theorem tailTrace_4150632 : CollatzResearch.WordTrace tailWord_4150632 prefixEnd_4150632 710423078644169955637199 := by
  unfold tailWord_4150632
  simp only [CollatzResearch.WordTrace]
  refine ⟨75692992949488305177283075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100923990599317740236377433 75692992949488305177283075)
  ·
    refine ⟨113539489424232457765924613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75692992949488305177283075 113539489424232457765924613)
    ·
      refine ⟨21288654267043585831110865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113539489424232457765924613 21288654267043585831110865)
      ·
        refine ⟨15966490700282689373333149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21288654267043585831110865 15966490700282689373333149)
        ·
          refine ⟨5987434012606008514999931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15966490700282689373333149 5987434012606008514999931)
          ·
            refine ⟨8981151018909012772499897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987434012606008514999931 8981151018909012772499897)
            ·
              refine ⟨6735863264181759579374923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8981151018909012772499897 6735863264181759579374923)
              ·
                refine ⟨10103794896272639369062385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735863264181759579374923 10103794896272639369062385)
                ·
                  refine ⟨7577846172204479526796789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10103794896272639369062385 7577846172204479526796789)
                  ·
                    refine ⟨710423078644169955637199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7577846172204479526796789 710423078644169955637199)
                    ·
                      rfl

theorem cell23_4150632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_4150632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150632 prefixEnd_4150632 := by exact prefixLift 4150632
  have htrace : WordTrace (prefixWord ++ tailWord_4150632) baseStart_4150632 baseEnd_4150632 := by
    simpa [prefixWord, tailWord_4150632, baseEnd_4150632] using wordTrace_append hprefix tailTrace_4150632
  have hstable : (prefixWord ++ tailWord_4150632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150632).length < 2 ^ (prefixWord ++ tailWord_4150632).sum := by decide
  have hdescent : baseEnd_4150632 < baseStart_4150632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150686 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4150686 : Nat := 118140960795 + 4150686 * 2 ^ 59
def prefixEnd_4150686 : Nat := 4983230072969 + 3 ^ 40 * 4150686 * 2
def baseEnd_4150686 : Nat := 2131296963887852655636349

theorem tailTrace_4150686 : CollatzResearch.WordTrace tailWord_4150686 prefixEnd_4150686 2131296963887852655636349 := by
  unfold tailWord_4150686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18923494430097622197128989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 100925303627187318384687941 18923494430097622197128989)
  ·
    refine ⟨7096310411286608323923371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18923494430097622197128989 7096310411286608323923371)
    ·
      refine ⟨10644465616929912485885057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096310411286608323923371 10644465616929912485885057)
      ·
        refine ⟨7983349212697434364413793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10644465616929912485885057 7983349212697434364413793)
        ·
          refine ⟨5987511909523075773310345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7983349212697434364413793 5987511909523075773310345)
          ·
            refine ⟨4490633932142306829982759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987511909523075773310345 4490633932142306829982759)
            ·
              refine ⟨6735950898213460244974139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490633932142306829982759 6735950898213460244974139)
              ·
                refine ⟨10103926347320190367461209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6735950898213460244974139 10103926347320190367461209)
                ·
                  refine ⟨7577944760490142775595907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10103926347320190367461209 7577944760490142775595907)
                  ·
                    refine ⟨11366917140735214163393861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7577944760490142775595907 11366917140735214163393861)
                    ·
                      refine ⟨2131296963887852655636349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11366917140735214163393861 2131296963887852655636349)
                      ·
                        rfl

theorem cell23_4150686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4150686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150686 prefixEnd_4150686 := by exact prefixLift 4150686
  have htrace : WordTrace (prefixWord ++ tailWord_4150686) baseStart_4150686 baseEnd_4150686 := by
    simpa [prefixWord, tailWord_4150686, baseEnd_4150686] using wordTrace_append hprefix tailTrace_4150686
  have hstable : (prefixWord ++ tailWord_4150686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150686).length < 2 ^ (prefixWord ++ tailWord_4150686).sum := by decide
  have hdescent : baseEnd_4150686 < baseStart_4150686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150712 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 2, 3, 2]
def baseStart_4150712 : Nat := 118140960795 + 4150712 * 2 ^ 59
def prefixEnd_4150712 : Nat := 4983230072969 + 3 ^ 40 * 4150712 * 2
def baseEnd_4150712 : Nat := 2131310314384869553911229

theorem tailTrace_4150712 : CollatzResearch.WordTrace tailWord_4150712 prefixEnd_4150712 2131310314384869553911229 := by
  unfold tailWord_4150712
  simp only [CollatzResearch.WordTrace]
  refine ⟨75694451869343392008739195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100925935825791189344985593 75694451869343392008739195)
  ·
    refine ⟨113541677804015088013108793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75694451869343392008739195 113541677804015088013108793)
    ·
      refine ⟨85156258353011316009831595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113541677804015088013108793 85156258353011316009831595)
      ·
        refine ⟨127734387529516974014747393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85156258353011316009831595 127734387529516974014747393)
        ·
          refine ⟨95800790647137730511060545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127734387529516974014747393 95800790647137730511060545)
          ·
            refine ⟨71850592985353297883295409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95800790647137730511060545 71850592985353297883295409)
            ·
              refine ⟨53887944739014973412471557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71850592985353297883295409 53887944739014973412471557)
              ·
                refine ⟨10103989638565307514838417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53887944739014973412471557 10103989638565307514838417)
                ·
                  refine ⟨7577992228923980636128813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10103989638565307514838417 7577992228923980636128813)
                  ·
                    refine ⟨2841747085846492738548305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7577992228923980636128813 2841747085846492738548305)
                    ·
                      refine ⟨2131310314384869553911229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841747085846492738548305 2131310314384869553911229)
                      ·
                        rfl

theorem cell23_4150712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_4150712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150712 prefixEnd_4150712 := by exact prefixLift 4150712
  have htrace : WordTrace (prefixWord ++ tailWord_4150712) baseStart_4150712 baseEnd_4150712 := by
    simpa [prefixWord, tailWord_4150712, baseEnd_4150712] using wordTrace_append hprefix tailTrace_4150712
  have hstable : (prefixWord ++ tailWord_4150712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150712).length < 2 ^ (prefixWord ++ tailWord_4150712).sum := by decide
  have hdescent : baseEnd_4150712 < baseStart_4150712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150735 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 1, 6]
def baseStart_4150735 : Nat := 118140960795 + 4150735 * 2 ^ 59
def prefixEnd_4150735 : Nat := 4983230072969 + 3 ^ 40 * 4150735 * 2
def baseEnd_4150735 : Nat := 710440708146640987974541

theorem tailTrace_4150735 : CollatzResearch.WordTrace tailWord_4150735 prefixEnd_4150735 710440708146640987974541 := by
  unfold tailWord_4150735
  simp only [CollatzResearch.WordTrace]
  refine ⟨151389742617603458945565659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100926495078402305963710439 151389742617603458945565659)
  ·
    refine ⟨227084613926405188418348489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151389742617603458945565659 227084613926405188418348489)
    ·
      refine ⟨170313460444803891313761367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 227084613926405188418348489 170313460444803891313761367)
      ·
        refine ⟨255470190667205836970642051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170313460444803891313761367 255470190667205836970642051)
        ·
          refine ⟨383205286000808755455963077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255470190667205836970642051 383205286000808755455963077)
          ·
            refine ⟨71850991125151641647993077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 383205286000808755455963077 71850991125151641647993077)
            ·
              refine ⟨6736030417982966404499351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71850991125151641647993077 6736030417982966404499351)
              ·
                refine ⟨10104045626974449606749027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736030417982966404499351 10104045626974449606749027)
                ·
                  refine ⟨15156068440461674410123541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10104045626974449606749027 15156068440461674410123541)
                  ·
                    refine ⟨710440708146640987974541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15156068440461674410123541 710440708146640987974541)
                    ·
                      rfl

theorem cell23_4150735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_4150735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150735 prefixEnd_4150735 := by exact prefixLift 4150735
  have htrace : WordTrace (prefixWord ++ tailWord_4150735) baseStart_4150735 baseEnd_4150735 := by
    simpa [prefixWord, tailWord_4150735, baseEnd_4150735] using wordTrace_append hprefix tailTrace_4150735
  have hstable : (prefixWord ++ tailWord_4150735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150735).length < 2 ^ (prefixWord ++ tailWord_4150735).sum := by decide
  have hdescent : baseEnd_4150735 < baseStart_4150735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150775 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_4150775 : Nat := 118140960795 + 4150775 * 2 ^ 59
def prefixEnd_4150775 : Nat := 4983230072969 + 3 ^ 40 * 4150775 * 2
def baseEnd_4150775 : Nat := 2131342663666102807423439

theorem tailTrace_4150775 : CollatzResearch.WordTrace tailWord_4150775 prefixEnd_4150775 2131342663666102807423439 := by
  unfold tailWord_4150775
  simp only [CollatzResearch.WordTrace]
  refine ⟨151391201537458545777021779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100927467691639030518014519 151391201537458545777021779)
  ·
    refine ⟨227086802306187818665532669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151391201537458545777021779 227086802306187818665532669)
    ·
      refine ⟨85157550864820431999574751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 227086802306187818665532669 85157550864820431999574751)
      ·
        refine ⟨127736326297230647999362127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85157550864820431999574751 127736326297230647999362127)
        ·
          refine ⟨191604489445845971999043191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127736326297230647999362127 191604489445845971999043191)
          ·
            refine ⟨287406734168768957998564787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191604489445845971999043191 287406734168768957998564787)
            ·
              refine ⟨431110101253153436997847181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287406734168768957998564787 431110101253153436997847181)
              ·
                refine ⟨161666287969932538874192693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431110101253153436997847181 161666287969932538874192693)
                ·
                  refine ⟨15156214497181175519455565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161666287969932538874192693 15156214497181175519455565)
                  ·
                    refine ⟨5683580436442940819795837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15156214497181175519455565 5683580436442940819795837)
                    ·
                      refine ⟨2131342663666102807423439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5683580436442940819795837 2131342663666102807423439)
                      ·
                        rfl

theorem cell23_4150775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_4150775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150775 prefixEnd_4150775 := by exact prefixLift 4150775
  have htrace : WordTrace (prefixWord ++ tailWord_4150775) baseStart_4150775 baseEnd_4150775 := by
    simpa [prefixWord, tailWord_4150775, baseEnd_4150775] using wordTrace_append hprefix tailTrace_4150775
  have hstable : (prefixWord ++ tailWord_4150775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150775).length < 2 ^ (prefixWord ++ tailWord_4150775).sum := by decide
  have hdescent : baseEnd_4150775 < baseStart_4150775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150776 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 3, 2, 2]
def baseStart_4150776 : Nat := 118140960795 + 4150776 * 2 ^ 59
def prefixEnd_4150776 : Nat := 4983230072969 + 3 ^ 40 * 4150776 * 2
def baseEnd_4150776 : Nat := 2131343177146757303510935

theorem tailTrace_4150776 : CollatzResearch.WordTrace tailWord_4150776 prefixEnd_4150776 2131343177146757303510935 := by
  unfold tailWord_4150776
  simp only [CollatzResearch.WordTrace]
  refine ⟨75695619005227461473904091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100927492006969948631872121 75695619005227461473904091)
  ·
    refine ⟨113543428507841192210856137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75695619005227461473904091 113543428507841192210856137)
    ·
      refine ⟨85157571380880894158142103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113543428507841192210856137 85157571380880894158142103)
      ·
        refine ⟨127736357071321341237213155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85157571380880894158142103 127736357071321341237213155)
        ·
          refine ⟨191604535606982011855819733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127736357071321341237213155 191604535606982011855819733)
          ·
            refine ⟨4490731303288640902870775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 191604535606982011855819733 4490731303288640902870775)
            ·
              refine ⟨6736096954932961354306163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490731303288640902870775 6736096954932961354306163)
              ·
                refine ⟨10104145432399442031459245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6736096954932961354306163 10104145432399442031459245)
                ·
                  refine ⟨3789054537149790761797217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10104145432399442031459245 3789054537149790761797217)
                  ·
                    refine ⟨2841790902862343071347913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3789054537149790761797217 2841790902862343071347913)
                    ·
                      refine ⟨2131343177146757303510935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841790902862343071347913 2131343177146757303510935)
                      ·
                        rfl

theorem cell23_4150776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_4150776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150776 prefixEnd_4150776 := by exact prefixLift 4150776
  have htrace : WordTrace (prefixWord ++ tailWord_4150776) baseStart_4150776 baseEnd_4150776 := by
    simpa [prefixWord, tailWord_4150776, baseEnd_4150776] using wordTrace_append hprefix tailTrace_4150776
  have hstable : (prefixWord ++ tailWord_4150776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150776).length < 2 ^ (prefixWord ++ tailWord_4150776).sum := by decide
  have hdescent : baseEnd_4150776 < baseStart_4150776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150786 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_4150786 : Nat := 118140960795 + 4150786 * 2 ^ 59
def prefixEnd_4150786 : Nat := 4983230072969 + 3 ^ 40 * 4150786 * 2
def baseEnd_4150786 : Nat := 710449437317767421461963

theorem tailTrace_4150786 : CollatzResearch.WordTrace tailWord_4150786 prefixEnd_4150786 710449437317767421461963 := by
  unfold tailWord_4150786
  simp only [CollatzResearch.WordTrace]
  refine ⟨37847900685104673663918053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100927735160279129770448141 37847900685104673663918053)
  ·
    refine ⟨7096481378457126311984635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37847900685104673663918053 7096481378457126311984635)
    ·
      refine ⟨10644722067685689467976953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7096481378457126311984635 10644722067685689467976953)
      ·
        refine ⟨7983541550764267100982715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10644722067685689467976953 7983541550764267100982715)
        ·
          refine ⟨11975312326146400651474073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7983541550764267100982715 11975312326146400651474073)
          ·
            refine ⟨8981484244609800488605555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11975312326146400651474073 8981484244609800488605555)
            ·
              refine ⟨13472226366914700732908333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8981484244609800488605555 13472226366914700732908333)
              ·
                refine ⟨5052084887593012774840625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13472226366914700732908333 5052084887593012774840625)
                ·
                  refine ⟨3789063665694759581130469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052084887593012774840625 3789063665694759581130469)
                  ·
                    refine ⟨710449437317767421461963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3789063665694759581130469 710449437317767421461963)
                    ·
                      rfl

theorem cell23_4150786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_4150786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150786 prefixEnd_4150786 := by exact prefixLift 4150786
  have htrace : WordTrace (prefixWord ++ tailWord_4150786) baseStart_4150786 baseEnd_4150786 := by
    simpa [prefixWord, tailWord_4150786, baseEnd_4150786] using wordTrace_append hprefix tailTrace_4150786
  have hstable : (prefixWord ++ tailWord_4150786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150786).length < 2 ^ (prefixWord ++ tailWord_4150786).sum := by decide
  have hdescent : baseEnd_4150786 < baseStart_4150786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150790 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4150790 : Nat := 118140960795 + 4150790 * 2 ^ 59
def prefixEnd_4150790 : Nat := 4983230072969 + 3 ^ 40 * 4150790 * 2
def baseEnd_4150790 : Nat := 710450121958640082911957

theorem tailTrace_4150790 : CollatzResearch.WordTrace tailWord_4150790 prefixEnd_4150790 710450121958640082911957 := by
  unfold tailWord_4150790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730992144762631354338057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 100927832421602802225878549 4730992144762631354338057)
  ·
    refine ⟨3548244108571973515753543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4730992144762631354338057 3548244108571973515753543)
    ·
      refine ⟨5322366162857960273630315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548244108571973515753543 5322366162857960273630315)
      ·
        refine ⟨7983549244286940410445473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5322366162857960273630315 7983549244286940410445473)
        ·
          refine ⟨5987661933215205307834105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7983549244286940410445473 5987661933215205307834105)
          ·
            refine ⟨4490746449911403980875579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987661933215205307834105 4490746449911403980875579)
            ·
              refine ⟨6736119674867105971313369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490746449911403980875579 6736119674867105971313369)
              ·
                refine ⟨5052089756150329478485027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736119674867105971313369 5052089756150329478485027)
                ·
                  refine ⟨7578134634225494217727541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052089756150329478485027 7578134634225494217727541)
                  ·
                    refine ⟨710450121958640082911957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7578134634225494217727541 710450121958640082911957)
                    ·
                      rfl

theorem cell23_4150790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4150790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150790 prefixEnd_4150790 := by exact prefixLift 4150790
  have htrace : WordTrace (prefixWord ++ tailWord_4150790) baseStart_4150790 baseEnd_4150790 := by
    simpa [prefixWord, tailWord_4150790, baseEnd_4150790] using wordTrace_append hprefix tailTrace_4150790
  have hstable : (prefixWord ++ tailWord_4150790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150790).length < 2 ^ (prefixWord ++ tailWord_4150790).sum := by decide
  have hdescent : baseEnd_4150790 < baseStart_4150790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150796 : List Nat := [2, 2, 1, 2, 5, 2, 1, 2, 1, 2, 3]
def baseStart_4150796 : Nat := 118140960795 + 4150796 * 2 ^ 59
def prefixEnd_4150796 : Nat := 4983230072969 + 3 ^ 40 * 4150796 * 2
def baseEnd_4150796 : Nat := 2131353446759847225260843

theorem tailTrace_4150796 : CollatzResearch.WordTrace tailWord_4150796 prefixEnd_4150796 2131353446759847225260843 := by
  unfold tailWord_4150796
  simp only [CollatzResearch.WordTrace]
  refine ⟨75695983735191233181768121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100927978313588310909024161 75695983735191233181768121)
  ·
    refine ⟨56771987801393424886326091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75695983735191233181768121 56771987801393424886326091)
    ·
      refine ⟨85157981702090137329489137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56771987801393424886326091 85157981702090137329489137)
      ·
        refine ⟨63868486276567602997116853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85157981702090137329489137 63868486276567602997116853)
        ·
          refine ⟨5987670588428212780979705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63868486276567602997116853 5987670588428212780979705)
          ·
            refine ⟨4490752941321159585734779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5987670588428212780979705 4490752941321159585734779)
            ·
              refine ⟨6736129411981739378602169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490752941321159585734779 6736129411981739378602169)
              ·
                refine ⟨5052097058986304533951627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736129411981739378602169 5052097058986304533951627)
                ·
                  refine ⟨7578145588479456800927441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5052097058986304533951627 7578145588479456800927441)
                  ·
                    refine ⟨5683609191359592600695581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7578145588479456800927441 5683609191359592600695581)
                    ·
                      refine ⟨2131353446759847225260843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5683609191359592600695581 2131353446759847225260843)
                      ·
                        rfl

theorem cell23_4150796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_4150796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150796 prefixEnd_4150796 := by exact prefixLift 4150796
  have htrace : WordTrace (prefixWord ++ tailWord_4150796) baseStart_4150796 baseEnd_4150796 := by
    simpa [prefixWord, tailWord_4150796, baseEnd_4150796] using wordTrace_append hprefix tailTrace_4150796
  have hstable : (prefixWord ++ tailWord_4150796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150796).length < 2 ^ (prefixWord ++ tailWord_4150796).sum := by decide
  have hdescent : baseEnd_4150796 < baseStart_4150796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150826 : List Nat := [3, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4150826 : Nat := 118140960795 + 4150826 * 2 ^ 59
def prefixEnd_4150826 : Nat := 4983230072969 + 3 ^ 40 * 4150826 * 2
def baseEnd_4150826 : Nat := 2131368851179482107885705

theorem tailTrace_4150826 : CollatzResearch.WordTrace tailWord_4150826 prefixEnd_4150826 2131368851179482107885705 := by
  unfold tailWord_4150826
  simp only [CollatzResearch.WordTrace]
  refine ⟨37848265415068445371782083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 100928707773515854324752221 37848265415068445371782083)
  ·
    refine ⟨56772398122602668057673125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37848265415068445371782083 56772398122602668057673125)
    ·
      refine ⟨10644824647988000260813711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56772398122602668057673125 10644824647988000260813711)
      ·
        refine ⟨15967236971982000391220567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10644824647988000260813711 15967236971982000391220567)
        ·
          refine ⟨23950855457973000586830851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15967236971982000391220567 23950855457973000586830851)
          ·
            refine ⟨35926283186959500880246277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23950855457973000586830851 35926283186959500880246277)
            ·
              refine ⟨6736178097554906415046177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35926283186959500880246277 6736178097554906415046177)
              ·
                refine ⟨5052133573166179811284633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736178097554906415046177 5052133573166179811284633)
                ·
                  refine ⟨3789100179874634858463475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052133573166179811284633 3789100179874634858463475)
                  ·
                    refine ⟨5683650269811952287695213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3789100179874634858463475 5683650269811952287695213)
                    ·
                      refine ⟨2131368851179482107885705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5683650269811952287695213 2131368851179482107885705)
                      ·
                        rfl

theorem cell23_4150826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4150826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150826 prefixEnd_4150826 := by exact prefixLift 4150826
  have htrace : WordTrace (prefixWord ++ tailWord_4150826) baseStart_4150826 baseEnd_4150826 := by
    simpa [prefixWord, tailWord_4150826, baseEnd_4150826] using wordTrace_append hprefix tailTrace_4150826
  have hstable : (prefixWord ++ tailWord_4150826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150826).length < 2 ^ (prefixWord ++ tailWord_4150826).sum := by decide
  have hdescent : baseEnd_4150826 < baseStart_4150826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150832 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 5, 4, 2]
def baseStart_4150832 : Nat := 118140960795 + 4150832 * 2 ^ 59
def prefixEnd_4150832 : Nat := 4983230072969 + 3 ^ 40 * 4150832 * 2
def baseEnd_4150832 : Nat := 2131371932063409084410677

theorem tailTrace_4150832 : CollatzResearch.WordTrace tailWord_4150832 prefixEnd_4150832 2131371932063409084410677 := by
  unfold tailWord_4150832
  simp only [CollatzResearch.WordTrace]
  refine ⟨75696640249126022255923375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 100928853665501363007897833 75696640249126022255923375)
  ·
    refine ⟨113544960373689033383885063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75696640249126022255923375 113544960373689033383885063)
    ·
      refine ⟨170317440560533550075827595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113544960373689033383885063 170317440560533550075827595)
      ·
        refine ⟨255476160840800325113741393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170317440560533550075827595 255476160840800325113741393)
        ·
          refine ⟨191607120630600243835306045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255476160840800325113741393 191607120630600243835306045)
          ·
            refine ⟨71852670236475091438239767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191607120630600243835306045 71852670236475091438239767)
            ·
              refine ⟨107779005354712637157359651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71852670236475091438239767 107779005354712637157359651)
              ·
                refine ⟨161668508032068955736039477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107779005354712637157359651 161668508032068955736039477)
                ·
                  refine ⟨15156422628006464600253701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161668508032068955736039477 15156422628006464600253701)
                  ·
                    refine ⟨2841829242751212112547569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15156422628006464600253701 2841829242751212112547569)
                    ·
                      refine ⟨2131371932063409084410677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2841829242751212112547569 2131371932063409084410677)
                      ·
                        rfl

theorem cell23_4150832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 5, 4, 2].length) (baseStart_4150832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150832 prefixEnd_4150832 := by exact prefixLift 4150832
  have htrace : WordTrace (prefixWord ++ tailWord_4150832) baseStart_4150832 baseEnd_4150832 := by
    simpa [prefixWord, tailWord_4150832, baseEnd_4150832] using wordTrace_append hprefix tailTrace_4150832
  have hstable : (prefixWord ++ tailWord_4150832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150832).length < 2 ^ (prefixWord ++ tailWord_4150832).sum := by decide
  have hdescent : baseEnd_4150832 < baseStart_4150832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4150877 : List Nat := [1, 4, 4, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4150877 : Nat := 118140960795 + 4150877 * 2 ^ 59
def prefixEnd_4150877 : Nat := 4983230072969 + 3 ^ 40 * 4150877 * 2
def baseEnd_4150877 : Nat := 2131395038692861408347971

theorem tailTrace_4150877 : CollatzResearch.WordTrace tailWord_4150877 prefixEnd_4150877 2131395038692861408347971 := by
  unfold tailWord_4150877
  simp only [CollatzResearch.WordTrace]
  refine ⟨151394921783089017197234885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 100929947855392678131489923 151394921783089017197234885)
  ·
    refine ⟨28386547834329190724481541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151394921783089017197234885 28386547834329190724481541)
    ·
      refine ⟨5322477718936723260840289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28386547834329190724481541 5322477718936723260840289)
      ·
        refine ⟨3991858289202542445630217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5322477718936723260840289 3991858289202542445630217)
        ·
          refine ⟨2993893716901906834222663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3991858289202542445630217 2993893716901906834222663)
          ·
            refine ⟨4490840575352860251333995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2993893716901906834222663 4490840575352860251333995)
            ·
              refine ⟨6736260863029290377000993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4490840575352860251333995 6736260863029290377000993)
              ·
                refine ⟨5052195647271967782750745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6736260863029290377000993 5052195647271967782750745)
                ·
                  refine ⟨3789146735453975837063059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5052195647271967782750745 3789146735453975837063059)
                  ·
                    refine ⟨5683720103180963755594589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3789146735453975837063059 5683720103180963755594589)
                    ·
                      refine ⟨2131395038692861408347971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5683720103180963755594589 2131395038692861408347971)
                      ·
                        rfl

theorem cell23_4150877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4150877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4150877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4150877 prefixEnd_4150877 := by exact prefixLift 4150877
  have htrace : WordTrace (prefixWord ++ tailWord_4150877) baseStart_4150877 baseEnd_4150877 := by
    simpa [prefixWord, tailWord_4150877, baseEnd_4150877] using wordTrace_append hprefix tailTrace_4150877
  have hstable : (prefixWord ++ tailWord_4150877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4150877).length < 2 ^ (prefixWord ++ tailWord_4150877).sum := by decide
  have hdescent : baseEnd_4150877 < baseStart_4150877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4150877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
