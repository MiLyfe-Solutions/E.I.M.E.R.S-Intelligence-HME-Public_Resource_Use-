import V185TrunkScan23Chunk0287

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1703125 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 1, 4]
def baseStart_1703125 : Nat := 118140960795 + 1703125 * 2 ^ 59
def prefixEnd_1703125 : Nat := 4983230072969 + 3 ^ 40 * 1703125 * 2
def baseEnd_1703125 : Nat := 291507246562918083101659

theorem tailTrace_1703125 : CollatzResearch.WordTrace tailWord_1703125 prefixEnd_1703125 291507246562918083101659 := by
  unfold tailWord_1703125
  simp only [CollatzResearch.WordTrace]
  refine ⟨62118071954876470437718829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41412047969917646958479219 62118071954876470437718829)
  ·
    refine ⟨23294276983078676414144561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62118071954876470437718829 23294276983078676414144561)
    ·
      refine ⟨17470707737309007310608421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23294276983078676414144561 17470707737309007310608421)
      ·
        refine ⟨3275757700745438870739079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17470707737309007310608421 3275757700745438870739079)
        ·
          refine ⟨4913636551118158306108619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275757700745438870739079 4913636551118158306108619)
          ·
            refine ⟨7370454826677237459162929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913636551118158306108619 7370454826677237459162929)
            ·
              refine ⟨5527841120007928094372197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7370454826677237459162929 5527841120007928094372197)
              ·
                refine ⟨1036470210001486517694787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5527841120007928094372197 1036470210001486517694787)
                ·
                  refine ⟨1554705315002229776542181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036470210001486517694787 1554705315002229776542181)
                  ·
                    refine ⟨291507246562918083101659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1554705315002229776542181 291507246562918083101659)
                    ·
                      rfl

theorem cell23_1703125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_1703125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703125 prefixEnd_1703125 := by exact prefixLift 1703125
  have htrace : WordTrace (prefixWord ++ tailWord_1703125) baseStart_1703125 baseEnd_1703125 := by
    simpa [prefixWord, tailWord_1703125, baseEnd_1703125] using wordTrace_append hprefix tailTrace_1703125
  have hstable : (prefixWord ++ tailWord_1703125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703125).length < 2 ^ (prefixWord ++ tailWord_1703125).sum := by decide
  have hdescent : baseEnd_1703125 < baseStart_1703125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703148 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 3]
def baseStart_1703148 : Nat := 118140960795 + 1703148 * 2 ^ 59
def prefixEnd_1703148 : Nat := 4983230072969 + 3 ^ 40 * 1703148 * 2
def baseEnd_1703148 : Nat := 874533549743807659317371

theorem tailTrace_1703148 : CollatzResearch.WordTrace tailWord_1703148 prefixEnd_1703148 874533549743807659317371 := by
  unfold tailWord_1703148
  simp only [CollatzResearch.WordTrace]
  refine ⟨31059455416896572682903049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41412607222528763577204065 31059455416896572682903049)
  ·
    refine ⟨23294591562672429512177287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31059455416896572682903049 23294591562672429512177287)
    ·
      refine ⟨34941887344008644268265931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23294591562672429512177287 34941887344008644268265931)
      ·
        refine ⟨52412831016012966402398897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34941887344008644268265931 52412831016012966402398897)
        ·
          refine ⟨39309623262009724801799173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52412831016012966402398897 39309623262009724801799173)
          ·
            refine ⟨7370554361626823400337345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39309623262009724801799173 7370554361626823400337345)
            ·
              refine ⟨5527915771220117550253009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7370554361626823400337345 5527915771220117550253009)
              ·
                refine ⟨4145936828415088162689757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5527915771220117550253009 4145936828415088162689757)
                ·
                  refine ⟨1554726310655658061008659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4145936828415088162689757 1554726310655658061008659)
                  ·
                    refine ⟨2332089465983487091512989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554726310655658061008659 2332089465983487091512989)
                    ·
                      refine ⟨874533549743807659317371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2332089465983487091512989 874533549743807659317371)
                      ·
                        rfl

theorem cell23_1703148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_1703148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703148 prefixEnd_1703148 := by exact prefixLift 1703148
  have htrace : WordTrace (prefixWord ++ tailWord_1703148) baseStart_1703148 baseEnd_1703148 := by
    simpa [prefixWord, tailWord_1703148, baseEnd_1703148] using wordTrace_append hprefix tailTrace_1703148
  have hstable : (prefixWord ++ tailWord_1703148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703148).length < 2 ^ (prefixWord ++ tailWord_1703148).sum := by decide
  have hdescent : baseEnd_1703148 < baseStart_1703148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703191 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 5]
def baseStart_1703191 : Nat := 118140960795 + 1703191 * 2 ^ 59
def prefixEnd_1703191 : Nat := 4983230072969 + 3 ^ 40 * 1703191 * 2
def baseEnd_1703191 : Nat := 874555629411950991079673

theorem tailTrace_1703191 : CollatzResearch.WordTrace tailWord_1703191 prefixEnd_1703191 874555629411950991079673 := by
  unfold tailWord_1703191
  simp only [CollatzResearch.WordTrace]
  refine ⟨62120479172637363709621427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41413652781758242473080951 62120479172637363709621427)
  ·
    refine ⟨93180718758956045564432141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62120479172637363709621427 93180718758956045564432141)
    ·
      refine ⟨34942769534608517086662053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93180718758956045564432141 34942769534608517086662053)
      ·
        refine ⟨6551769287739096953749135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34942769534608517086662053 6551769287739096953749135)
        ·
          refine ⟨9827653931608645430623703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551769287739096953749135 9827653931608645430623703)
          ·
            refine ⟨14741480897412968145935555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9827653931608645430623703 14741480897412968145935555)
            ·
              refine ⟨22112221346119452218903333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14741480897412968145935555 22112221346119452218903333)
              ·
                refine ⟨4146041502397397291044375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22112221346119452218903333 4146041502397397291044375)
                ·
                  refine ⟨6219062253596095936566563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146041502397397291044375 6219062253596095936566563)
                  ·
                    refine ⟨9328593380394143904849845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219062253596095936566563 9328593380394143904849845)
                    ·
                      refine ⟨874555629411950991079673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9328593380394143904849845 874555629411950991079673)
                      ·
                        rfl

theorem cell23_1703191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_1703191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703191 prefixEnd_1703191 := by exact prefixLift 1703191
  have htrace : WordTrace (prefixWord ++ tailWord_1703191) baseStart_1703191 baseEnd_1703191 := by
    simpa [prefixWord, tailWord_1703191, baseEnd_1703191] using wordTrace_append hprefix tailTrace_1703191
  have hstable : (prefixWord ++ tailWord_1703191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703191).length < 2 ^ (prefixWord ++ tailWord_1703191).sum := by decide
  have hdescent : baseEnd_1703191 < baseStart_1703191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703201 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1703201 : Nat := 118140960795 + 1703201 * 2 ^ 59
def prefixEnd_1703201 : Nat := 4983230072969 + 3 ^ 40 * 1703201 * 2
def baseEnd_1703201 : Nat := 874560764218495951954627

theorem tailTrace_1703201 : CollatzResearch.WordTrace tailWord_1703201 prefixEnd_1703201 874560764218495951954627 := by
  unfold tailWord_1703201
  simp only [CollatzResearch.WordTrace]
  refine ⟨62120843902601135417485457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41413895935067423611656971 62120843902601135417485457)
  ·
    refine ⟨46590632926950851563114093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62120843902601135417485457 46590632926950851563114093)
    ·
      refine ⟨17471487347606569336167785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46590632926950851563114093 17471487347606569336167785)
      ·
        refine ⟨13103615510704927002125839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17471487347606569336167785 13103615510704927002125839)
        ·
          refine ⟨19655423266057390503188759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13103615510704927002125839 19655423266057390503188759)
          ·
            refine ⟨29483134899086085754783139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19655423266057390503188759 29483134899086085754783139)
            ·
              refine ⟨44224702348629128632174709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29483134899086085754783139 44224702348629128632174709)
              ·
                refine ⟨4146065845183980809266379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44224702348629128632174709 4146065845183980809266379)
                ·
                  refine ⟨6219098767775971213899569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146065845183980809266379 6219098767775971213899569)
                  ·
                    refine ⟨4664324075831978410424677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6219098767775971213899569 4664324075831978410424677)
                    ·
                      refine ⟨874560764218495951954627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4664324075831978410424677 874560764218495951954627)
                      ·
                        rfl

theorem cell23_1703201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1703201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703201 prefixEnd_1703201 := by exact prefixLift 1703201
  have htrace : WordTrace (prefixWord ++ tailWord_1703201) baseStart_1703201 baseEnd_1703201 := by
    simpa [prefixWord, tailWord_1703201, baseEnd_1703201] using wordTrace_append hprefix tailTrace_1703201
  have hstable : (prefixWord ++ tailWord_1703201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703201).length < 2 ^ (prefixWord ++ tailWord_1703201).sum := by decide
  have hdescent : baseEnd_1703201 < baseStart_1703201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703202 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_1703202 : Nat := 118140960795 + 1703202 * 2 ^ 59
def prefixEnd_1703202 : Nat := 4983230072969 + 3 ^ 40 * 1703202 * 2
def baseEnd_1703202 : Nat := 291520425899716816014041

theorem tailTrace_1703202 : CollatzResearch.WordTrace tailWord_1703202 prefixEnd_1703202 291520425899716816014041 := by
  unfold tailWord_1703202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15530220093899378147067965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41413920250398341725514573 15530220093899378147067965)
  ·
    refine ⟨5823832535212266805150487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15530220093899378147067965 5823832535212266805150487)
    ·
      refine ⟨8735748802818400207725731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823832535212266805150487 8735748802818400207725731)
      ·
        refine ⟨13103623204227600311588597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735748802818400207725731 13103623204227600311588597)
        ·
          refine ⟨1228464675396337529211431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13103623204227600311588597 1228464675396337529211431)
          ·
            refine ⟨1842697013094506293817147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228464675396337529211431 1842697013094506293817147)
            ·
              refine ⟨2764045519641759440725721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842697013094506293817147 2764045519641759440725721)
              ·
                refine ⟨2073034139731319580544291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764045519641759440725721 2073034139731319580544291)
                ·
                  refine ⟨3109551209596979370816437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073034139731319580544291 3109551209596979370816437)
                  ·
                    refine ⟨291520425899716816014041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3109551209596979370816437 291520425899716816014041)
                    ·
                      rfl

theorem cell23_1703202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_1703202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703202 prefixEnd_1703202 := by exact prefixLift 1703202
  have htrace : WordTrace (prefixWord ++ tailWord_1703202) baseStart_1703202 baseEnd_1703202 := by
    simpa [prefixWord, tailWord_1703202, baseEnd_1703202] using wordTrace_append hprefix tailTrace_1703202
  have hstable : (prefixWord ++ tailWord_1703202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703202).length < 2 ^ (prefixWord ++ tailWord_1703202).sum := by decide
  have hdescent : baseEnd_1703202 < baseStart_1703202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703205 : List Nat := [1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_1703205 : Nat := 118140960795 + 1703205 * 2 ^ 59
def prefixEnd_1703205 : Nat := 4983230072969 + 3 ^ 40 * 1703205 * 2
def baseEnd_1703205 : Nat := 874562818141113936304609

theorem tailTrace_1703205 : CollatzResearch.WordTrace tailWord_1703205 prefixEnd_1703205 874562818141113936304609 := by
  unfold tailWord_1703205
  simp only [CollatzResearch.WordTrace]
  refine ⟨62120989794586644100631069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41413993196391096067087379 62120989794586644100631069)
  ·
    refine ⟨23295371172969991537736651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62120989794586644100631069 23295371172969991537736651)
    ·
      refine ⟨34943056759454987306604977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23295371172969991537736651 34943056759454987306604977)
      ·
        refine ⟨26207292569591240479953733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34943056759454987306604977 26207292569591240479953733)
        ·
          refine ⟨4913867356798357589991325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26207292569591240479953733 4913867356798357589991325)
          ·
            refine ⟨1842700258799384096246747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4913867356798357589991325 1842700258799384096246747)
            ·
              refine ⟨2764050388199076144370121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842700258799384096246747 2764050388199076144370121)
              ·
                refine ⟨2073037791149307108277591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764050388199076144370121 2073037791149307108277591)
                ·
                  refine ⟨3109556686723960662416387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2073037791149307108277591 3109556686723960662416387)
                  ·
                    refine ⟨4664335030085940993624581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3109556686723960662416387 4664335030085940993624581)
                    ·
                      refine ⟨874562818141113936304609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4664335030085940993624581 874562818141113936304609)
                      ·
                        rfl

theorem cell23_1703205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_1703205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703205 prefixEnd_1703205 := by exact prefixLift 1703205
  have htrace : WordTrace (prefixWord ++ tailWord_1703205) baseStart_1703205 baseEnd_1703205 := by
    simpa [prefixWord, tailWord_1703205, baseEnd_1703205] using wordTrace_append hprefix tailTrace_1703205
  have hstable : (prefixWord ++ tailWord_1703205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703205).length < 2 ^ (prefixWord ++ tailWord_1703205).sum := by decide
  have hdescent : baseEnd_1703205 < baseStart_1703205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703218 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4]
def baseStart_1703218 : Nat := 118140960795 + 1703218 * 2 ^ 59
def prefixEnd_1703218 : Nat := 4983230072969 + 3 ^ 40 * 1703218 * 2
def baseEnd_1703218 : Nat := 874569493389622385442049

theorem tailTrace_1703218 : CollatzResearch.WordTrace tailWord_1703218 prefixEnd_1703218 874569493389622385442049 := by
  unfold tailWord_1703218
  simp only [CollatzResearch.WordTrace]
  refine ⟨15530365985884886830213577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41414309295693031547236205 15530365985884886830213577)
  ·
    refine ⟨11647774489413665122660183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15530365985884886830213577 11647774489413665122660183)
    ·
      refine ⟨17471661734120497683990275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11647774489413665122660183 17471661734120497683990275)
      ·
        refine ⟨26207492601180746525985413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17471661734120497683990275 26207492601180746525985413)
        ·
          refine ⟨4913904862721389973622265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26207492601180746525985413 4913904862721389973622265)
          ·
            refine ⟨3685428647041042480216699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4913904862721389973622265 3685428647041042480216699)
            ·
              refine ⟨5528142970561563720325049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3685428647041042480216699 5528142970561563720325049)
              ·
                refine ⟨4146107227921172790243787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528142970561563720325049 4146107227921172790243787)
                ·
                  refine ⟨6219160841881759185365681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146107227921172790243787 6219160841881759185365681)
                  ·
                    refine ⟨4664370631411319389024261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6219160841881759185365681 4664370631411319389024261)
                    ·
                      refine ⟨874569493389622385442049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4664370631411319389024261 874569493389622385442049)
                      ·
                        rfl

theorem cell23_1703218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_1703218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703218 prefixEnd_1703218 := by exact prefixLift 1703218
  have htrace : WordTrace (prefixWord ++ tailWord_1703218) baseStart_1703218 baseEnd_1703218 := by
    simpa [prefixWord, tailWord_1703218, baseEnd_1703218] using wordTrace_append hprefix tailTrace_1703218
  have hstable : (prefixWord ++ tailWord_1703218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703218).length < 2 ^ (prefixWord ++ tailWord_1703218).sum := by decide
  have hdescent : baseEnd_1703218 < baseStart_1703218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703225 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1703225 : Nat := 118140960795 + 1703225 * 2 ^ 59
def prefixEnd_1703225 : Nat := 4983230072969 + 3 ^ 40 * 1703225 * 2
def baseEnd_1703225 : Nat := 874573087754203858054517

theorem tailTrace_1703225 : CollatzResearch.WordTrace tailWord_1703225 prefixEnd_1703225 874573087754203858054517 := by
  unfold tailWord_1703225
  simp only [CollatzResearch.WordTrace]
  refine ⟨62121719254514187516359129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41414479503009458344239419 62121719254514187516359129)
  ·
    refine ⟨46591289440885640637269347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62121719254514187516359129 46591289440885640637269347)
    ·
      refine ⟨69886934161328460955904021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46591289440885640637269347 69886934161328460955904021)
      ·
        refine ⟨3275950038812271607308001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69886934161328460955904021 3275950038812271607308001)
        ·
          refine ⟨2456962529109203705481001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3275950038812271607308001 2456962529109203705481001)
          ·
            refine ⟨1842721896831902779110751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2456962529109203705481001 1842721896831902779110751)
            ·
              refine ⟨2764082845247854168666127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842721896831902779110751 2764082845247854168666127)
              ·
                refine ⟨4146124267871781252999191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764082845247854168666127 4146124267871781252999191)
                ·
                  refine ⟨6219186401807671879498787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146124267871781252999191 6219186401807671879498787)
                  ·
                    refine ⟨9328779602711507819248181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219186401807671879498787 9328779602711507819248181)
                    ·
                      refine ⟨874573087754203858054517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9328779602711507819248181 874573087754203858054517)
                      ·
                        rfl

theorem cell23_1703225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1703225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703225 prefixEnd_1703225 := by exact prefixLift 1703225
  have htrace : WordTrace (prefixWord ++ tailWord_1703225) baseStart_1703225 baseEnd_1703225 := by
    simpa [prefixWord, tailWord_1703225, baseEnd_1703225] using wordTrace_append hprefix tailTrace_1703225
  have hstable : (prefixWord ++ tailWord_1703225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703225).length < 2 ^ (prefixWord ++ tailWord_1703225).sum := by decide
  have hdescent : baseEnd_1703225 < baseStart_1703225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703239 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_1703239 : Nat := 118140960795 + 1703239 * 2 ^ 59
def prefixEnd_1703239 : Nat := 4983230072969 + 3 ^ 40 * 1703239 * 2
def baseEnd_1703239 : Nat := 874580276483366803279453

theorem tailTrace_1703239 : CollatzResearch.WordTrace tailWord_1703239 prefixEnd_1703239 874580276483366803279453 := by
  unfold tailWord_1703239
  simp only [CollatzResearch.WordTrace]
  refine ⟨62122229876463467907368771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41414819917642311938245847 62122229876463467907368771)
  ·
    refine ⟨93183344814695201861053157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62122229876463467907368771 93183344814695201861053157)
    ·
      refine ⟨17471877152755350348947467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93183344814695201861053157 17471877152755350348947467)
      ·
        refine ⟨26207815729133025523421201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17471877152755350348947467 26207815729133025523421201)
        ·
          refine ⟨19655861796849769142565901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26207815729133025523421201 19655861796849769142565901)
          ·
            refine ⟨7370948173818663428462213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19655861796849769142565901 7370948173818663428462213)
            ·
              refine ⟨1382052782590999392836665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7370948173818663428462213 1382052782590999392836665)
              ·
                refine ⟨1036539586943249544627499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382052782590999392836665 1036539586943249544627499)
                ·
                  refine ⟨1554809380414874316941249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036539586943249544627499 1554809380414874316941249)
                  ·
                    refine ⟨1166107035311155737705937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1554809380414874316941249 1166107035311155737705937)
                    ·
                      refine ⟨874580276483366803279453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166107035311155737705937 874580276483366803279453)
                      ·
                        rfl

theorem cell23_1703239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_1703239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703239 prefixEnd_1703239 := by exact prefixLift 1703239
  have htrace : WordTrace (prefixWord ++ tailWord_1703239) baseStart_1703239 baseEnd_1703239 := by
    simpa [prefixWord, tailWord_1703239, baseEnd_1703239] using wordTrace_append hprefix tailTrace_1703239
  have hstable : (prefixWord ++ tailWord_1703239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703239).length < 2 ^ (prefixWord ++ tailWord_1703239).sum := by decide
  have hdescent : baseEnd_1703239 < baseStart_1703239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703248 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 5, 3, 2]
def baseStart_1703248 : Nat := 118140960795 + 1703248 * 2 ^ 59
def prefixEnd_1703248 : Nat := 4983230072969 + 3 ^ 40 * 1703248 * 2
def baseEnd_1703248 : Nat := 874584897809257268066911

theorem tailTrace_1703248 : CollatzResearch.WordTrace tailWord_1703248 prefixEnd_1703248 874584897809257268066911 := by
  unfold tailWord_1703248
  simp only [CollatzResearch.WordTrace]
  refine ⟨31061279066715431222223199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41415038755620574962964265 31061279066715431222223199)
  ·
    refine ⟨46591918600073146833334799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31061279066715431222223199 46591918600073146833334799)
    ·
      refine ⟨69887877900109720250002199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46591918600073146833334799 69887877900109720250002199)
      ·
        refine ⟨104831816850164580375003299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69887877900109720250002199 104831816850164580375003299)
        ·
          refine ⟨157247725275246870562504949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104831816850164580375003299 157247725275246870562504949)
          ·
            refine ⟨14741974244554394115234839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157247725275246870562504949 14741974244554394115234839)
            ·
              refine ⟨22112961366831591172852259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14741974244554394115234839 22112961366831591172852259)
              ·
                refine ⟨33169442050247386759278389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22112961366831591172852259 33169442050247386759278389)
                ·
                  refine ⟨3109635192210692508682349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33169442050247386759278389 3109635192210692508682349)
                  ·
                    refine ⟨1166113197079009690755881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3109635192210692508682349 1166113197079009690755881)
                    ·
                      refine ⟨874584897809257268066911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166113197079009690755881 874584897809257268066911)
                      ·
                        rfl

theorem cell23_1703248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 5, 3, 2].length) (baseStart_1703248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703248 prefixEnd_1703248 := by exact prefixLift 1703248
  have htrace : WordTrace (prefixWord ++ tailWord_1703248) baseStart_1703248 baseEnd_1703248 := by
    simpa [prefixWord, tailWord_1703248, baseEnd_1703248] using wordTrace_append hprefix tailTrace_1703248
  have hstable : (prefixWord ++ tailWord_1703248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703248).length < 2 ^ (prefixWord ++ tailWord_1703248).sum := by decide
  have hdescent : baseEnd_1703248 < baseStart_1703248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703255 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 3]
def baseStart_1703255 : Nat := 118140960795 + 1703255 * 2 ^ 59
def prefixEnd_1703255 : Nat := 4983230072969 + 3 ^ 40 * 1703255 * 2
def baseEnd_1703255 : Nat := 874588492173838740679379

theorem tailTrace_1703255 : CollatzResearch.WordTrace tailWord_1703255 prefixEnd_1703255 874588492173838740679379 := by
  unfold tailWord_1703255
  simp only [CollatzResearch.WordTrace]
  refine ⟨62122813444405502639951219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41415208962937001759967479 62122813444405502639951219)
  ·
    refine ⟨93184220166608253959926829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62122813444405502639951219 93184220166608253959926829)
    ·
      refine ⟨34944082562478095234972561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93184220166608253959926829 34944082562478095234972561)
      ·
        refine ⟨26208061921858571426229421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34944082562478095234972561 26208061921858571426229421)
        ·
          refine ⟨9828023220696964284836033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26208061921858571426229421 9828023220696964284836033)
          ·
            refine ⟨7371017415522723213627025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9828023220696964284836033 7371017415522723213627025)
            ·
              refine ⟨5528263061642042410220269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7371017415522723213627025 5528263061642042410220269)
              ·
                refine ⟨2073098648115765903832601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5528263061642042410220269 2073098648115765903832601)
                ·
                  refine ⟨1554823986086824427874451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2073098648115765903832601 1554823986086824427874451)
                  ·
                    refine ⟨2332235979130236641811677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1554823986086824427874451 2332235979130236641811677)
                    ·
                      refine ⟨874588492173838740679379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2332235979130236641811677 874588492173838740679379)
                      ·
                        rfl

theorem cell23_1703255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 2, 1, 3].length) (baseStart_1703255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703255 prefixEnd_1703255 := by exact prefixLift 1703255
  have htrace : WordTrace (prefixWord ++ tailWord_1703255) baseStart_1703255 baseEnd_1703255 := by
    simpa [prefixWord, tailWord_1703255, baseEnd_1703255] using wordTrace_append hprefix tailTrace_1703255
  have hstable : (prefixWord ++ tailWord_1703255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703255).length < 2 ^ (prefixWord ++ tailWord_1703255).sum := by decide
  have hdescent : baseEnd_1703255 < baseStart_1703255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703281 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1703281 : Nat := 118140960795 + 1703281 * 2 ^ 59
def prefixEnd_1703281 : Nat := 4983230072969 + 3 ^ 40 * 1703281 * 2
def baseEnd_1703281 : Nat := 874601842670855638954259

theorem tailTrace_1703281 : CollatzResearch.WordTrace tailWord_1703281 prefixEnd_1703281 874601842670855638954259 := by
  unfold tailWord_1703281
  simp only [CollatzResearch.WordTrace]
  refine ⟨62123761742311309080397697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41415841161540872720265131 62123761742311309080397697)
  ·
    refine ⟨46592821306733481810298273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62123761742311309080397697 46592821306733481810298273)
    ·
      refine ⟨34944615980050111357723705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46592821306733481810298273 34944615980050111357723705)
      ·
        refine ⟨26208461985037583518292779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34944615980050111357723705 26208461985037583518292779)
        ·
          refine ⟨39312692977556375277439169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26208461985037583518292779 39312692977556375277439169)
          ·
            refine ⟨29484519733167281458079377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39312692977556375277439169 29484519733167281458079377)
            ·
              refine ⟨22113389799875461093559533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29484519733167281458079377 22113389799875461093559533)
              ·
                refine ⟨8292521174953297910084825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22113389799875461093559533 8292521174953297910084825)
                ·
                  refine ⟨6219390881214973432563619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8292521174953297910084825 6219390881214973432563619)
                  ·
                    refine ⟨9329086321822460148845429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219390881214973432563619 9329086321822460148845429)
                    ·
                      refine ⟨874601842670855638954259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9329086321822460148845429 874601842670855638954259)
                      ·
                        rfl

theorem cell23_1703281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1703281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703281 prefixEnd_1703281 := by exact prefixLift 1703281
  have htrace : WordTrace (prefixWord ++ tailWord_1703281) baseStart_1703281 baseEnd_1703281 := by
    simpa [prefixWord, tailWord_1703281, baseEnd_1703281] using wordTrace_append hprefix tailTrace_1703281
  have hstable : (prefixWord ++ tailWord_1703281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703281).length < 2 ^ (prefixWord ++ tailWord_1703281).sum := by decide
  have hdescent : baseEnd_1703281 < baseStart_1703281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703291 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4]
def baseStart_1703291 : Nat := 118140960795 + 1703291 * 2 ^ 59
def prefixEnd_1703291 : Nat := 4983230072969 + 3 ^ 40 * 1703291 * 2
def baseEnd_1703291 : Nat := 874606977477400599829213

theorem tailTrace_1703291 : CollatzResearch.WordTrace tailWord_1703291 prefixEnd_1703291 874606977477400599829213 := by
  unfold tailWord_1703291
  simp only [CollatzResearch.WordTrace]
  refine ⟨62124126472275080788261727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41416084314850053858841151 62124126472275080788261727)
  ·
    refine ⟨93186189708412621182392591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62124126472275080788261727 93186189708412621182392591)
    ·
      refine ⟨139779284562618931773588887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93186189708412621182392591 139779284562618931773588887)
      ·
        refine ⟨209668926843928397660383331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139779284562618931773588887 209668926843928397660383331)
        ·
          refine ⟨314503390265892596490574997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209668926843928397660383331 314503390265892596490574997)
          ·
            refine ⟨14742346418713715460495703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314503390265892596490574997 14742346418713715460495703)
            ·
              refine ⟨22113519628070573190743555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14742346418713715460495703 22113519628070573190743555)
              ·
                refine ⟨33170279442105859786115333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22113519628070573190743555 33170279442105859786115333)
                ·
                  refine ⟨6219427395394848709896625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33170279442105859786115333 6219427395394848709896625)
                  ·
                    refine ⟨4664570546546136532422469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6219427395394848709896625 4664570546546136532422469)
                    ·
                      refine ⟨874606977477400599829213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4664570546546136532422469 874606977477400599829213)
                      ·
                        rfl

theorem cell23_1703291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 4].length) (baseStart_1703291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703291 prefixEnd_1703291 := by exact prefixLift 1703291
  have htrace : WordTrace (prefixWord ++ tailWord_1703291) baseStart_1703291 baseEnd_1703291 := by
    simpa [prefixWord, tailWord_1703291, baseEnd_1703291] using wordTrace_append hprefix tailTrace_1703291
  have hstable : (prefixWord ++ tailWord_1703291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703291).length < 2 ^ (prefixWord ++ tailWord_1703291).sum := by decide
  have hdescent : baseEnd_1703291 < baseStart_1703291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703301 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 7]
def baseStart_1703301 : Nat := 118140960795 + 1703301 * 2 ^ 59
def prefixEnd_1703301 : Nat := 4983230072969 + 3 ^ 40 * 1703301 * 2
def baseEnd_1703301 : Nat := 97179123587105062300463

theorem tailTrace_1703301 : CollatzResearch.WordTrace tailWord_1703301 prefixEnd_1703301 97179123587105062300463 := by
  unfold tailWord_1703301
  simp only [CollatzResearch.WordTrace]
  refine ⟨62124491202238852496125757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41416327468159234997417171 62124491202238852496125757)
  ·
    refine ⟨23296684200839569686047159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62124491202238852496125757 23296684200839569686047159)
    ·
      refine ⟨34945026301259354529070739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23296684200839569686047159 34945026301259354529070739)
      ·
        refine ⟨52417539451889031793606109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34945026301259354529070739 52417539451889031793606109)
        ·
          refine ⟨19656577294458386922602291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52417539451889031793606109 19656577294458386922602291)
          ·
            refine ⟨29484865941687580383903437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19656577294458386922602291 29484865941687580383903437)
            ·
              refine ⟨11056824728132842643963789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29484865941687580383903437 11056824728132842643963789)
              ·
                refine ⟨4146309273049815991486421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11056824728132842643963789 4146309273049815991486421)
                ·
                  refine ⟨97179123587105062300463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4146309273049815991486421 97179123587105062300463)
                  ·
                    rfl

theorem cell23_1703301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_1703301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703301 prefixEnd_1703301 := by exact prefixLift 1703301
  have htrace : WordTrace (prefixWord ++ tailWord_1703301) baseStart_1703301 baseEnd_1703301 := by
    simpa [prefixWord, tailWord_1703301, baseEnd_1703301] using wordTrace_append hprefix tailTrace_1703301
  have hstable : (prefixWord ++ tailWord_1703301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703301).length < 2 ^ (prefixWord ++ tailWord_1703301).sum := by decide
  have hdescent : baseEnd_1703301 < baseStart_1703301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703331 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 1, 7]
def baseStart_1703331 : Nat := 118140960795 + 1703331 * 2 ^ 59
def prefixEnd_1703331 : Nat := 4983230072969 + 3 ^ 40 * 1703331 * 2
def baseEnd_1703331 : Nat := 291542505567860147776343

theorem tailTrace_1703331 : CollatzResearch.WordTrace tailWord_1703331 prefixEnd_1703331 291542505567860147776343 := by
  unfold tailWord_1703331
  simp only [CollatzResearch.WordTrace]
  refine ⟨62125585392130167619717847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41417056928086778413145231 62125585392130167619717847)
  ·
    refine ⟨93188378088195251429576771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62125585392130167619717847 93188378088195251429576771)
    ·
      refine ⟨139782567132292877144365157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93188378088195251429576771 139782567132292877144365157)
      ·
        refine ⟨26209231337304914464568467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139782567132292877144365157 26209231337304914464568467)
        ·
          refine ⟨39313847005957371696852701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26209231337304914464568467 39313847005957371696852701)
          ·
            refine ⟨14742692627234014386319763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39313847005957371696852701 14742692627234014386319763)
            ·
              refine ⟨22114038940851021579479645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14742692627234014386319763 22114038940851021579479645)
              ·
                refine ⟨8292764602819133092304867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22114038940851021579479645 8292764602819133092304867)
                ·
                  refine ⟨12439146904228699638457301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8292764602819133092304867 12439146904228699638457301)
                  ·
                    refine ⟨291542505567860147776343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12439146904228699638457301 291542505567860147776343)
                    ·
                      rfl

theorem cell23_1703331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 7].length) (baseStart_1703331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703331 prefixEnd_1703331 := by exact prefixLift 1703331
  have htrace : WordTrace (prefixWord ++ tailWord_1703331) baseStart_1703331 baseEnd_1703331 := by
    simpa [prefixWord, tailWord_1703331, baseEnd_1703331] using wordTrace_append hprefix tailTrace_1703331
  have hstable : (prefixWord ++ tailWord_1703331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703331).length < 2 ^ (prefixWord ++ tailWord_1703331).sum := by decide
  have hdescent : baseEnd_1703331 < baseStart_1703331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703368 : List Nat := [2, 1, 3, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1703368 : Nat := 118140960795 + 1703368 * 2 ^ 59
def prefixEnd_1703368 : Nat := 4983230072969 + 3 ^ 40 * 1703368 * 2
def baseEnd_1703368 : Nat := 874646515487796798566359

theorem tailTrace_1703368 : CollatzResearch.WordTrace tailWord_1703368 prefixEnd_1703368 874646515487796798566359 := by
  unfold tailWord_1703368
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063467446498061469407379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41417956595330748625876505 31063467446498061469407379)
  ·
    refine ⟨46595201169747092204111069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31063467446498061469407379 46595201169747092204111069)
    ·
      refine ⟨17473200438655159576541651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46595201169747092204111069 17473200438655159576541651)
      ·
        refine ⟨26209800657982739364812477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17473200438655159576541651 26209800657982739364812477)
        ·
          refine ⟨9828675246743527261804679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26209800657982739364812477 9828675246743527261804679)
          ·
            refine ⟨14743012870115290892707019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9828675246743527261804679 14743012870115290892707019)
            ·
              refine ⟨22114519305172936339060529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14743012870115290892707019 22114519305172936339060529)
              ·
                refine ⟨16585889478879702254295397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22114519305172936339060529 16585889478879702254295397)
                ·
                  refine ⟨3109854277289944172680387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16585889478879702254295397 3109854277289944172680387)
                  ·
                    refine ⟨4664781415934916259020581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3109854277289944172680387 4664781415934916259020581)
                    ·
                      refine ⟨874646515487796798566359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4664781415934916259020581 874646515487796798566359)
                      ·
                        rfl

theorem cell23_1703368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1703368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703368 prefixEnd_1703368 := by exact prefixLift 1703368
  have htrace : WordTrace (prefixWord ++ tailWord_1703368) baseStart_1703368 baseEnd_1703368 := by
    simpa [prefixWord, tailWord_1703368, baseEnd_1703368] using wordTrace_append hprefix tailTrace_1703368
  have hstable : (prefixWord ++ tailWord_1703368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703368).length < 2 ^ (prefixWord ++ tailWord_1703368).sum := by decide
  have hdescent : baseEnd_1703368 < baseStart_1703368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703382 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1703382 : Nat := 118140960795 + 1703382 * 2 ^ 59
def prefixEnd_1703382 : Nat := 4983230072969 + 3 ^ 40 * 1703382 * 2
def baseEnd_1703382 : Nat := 291551234738986581263765

theorem tailTrace_1703382 : CollatzResearch.WordTrace tailWord_1703382 prefixEnd_1703382 291551234738986581263765 := by
  unfold tailWord_1703382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3882965344684087708114025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41418297009963602219882933 3882965344684087708114025)
  ·
    refine ⟨2912224008513065781085519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3882965344684087708114025 2912224008513065781085519)
    ·
      refine ⟨4368336012769598671628279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912224008513065781085519 4368336012769598671628279)
      ·
        refine ⟨6552504019154398007442419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4368336012769598671628279 6552504019154398007442419)
        ·
          refine ⟨9828756028731597011163629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552504019154398007442419 9828756028731597011163629)
          ·
            refine ⟨3685783510774348879186361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9828756028731597011163629 3685783510774348879186361)
            ·
              refine ⟨2764337633080761659389771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685783510774348879186361 2764337633080761659389771)
              ·
                refine ⟨4146506449621142489084657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764337633080761659389771 4146506449621142489084657)
                ·
                  refine ⟨3109879837215856866813493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146506449621142489084657 3109879837215856866813493)
                  ·
                    refine ⟨291551234738986581263765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3109879837215856866813493 291551234738986581263765)
                    ·
                      rfl

theorem cell23_1703382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1703382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703382 prefixEnd_1703382 := by exact prefixLift 1703382
  have htrace : WordTrace (prefixWord ++ tailWord_1703382) baseStart_1703382 baseEnd_1703382 := by
    simpa [prefixWord, tailWord_1703382, baseEnd_1703382] using wordTrace_append hprefix tailTrace_1703382
  have hstable : (prefixWord ++ tailWord_1703382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703382).length < 2 ^ (prefixWord ++ tailWord_1703382).sum := by decide
  have hdescent : baseEnd_1703382 < baseStart_1703382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703385 : List Nat := [1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 4]
def baseStart_1703385 : Nat := 118140960795 + 1703385 * 2 ^ 59
def prefixEnd_1703385 : Nat := 4983230072969 + 3 ^ 40 * 1703385 * 2
def baseEnd_1703385 : Nat := 874655244658923232053781

theorem tailTrace_1703385 : CollatzResearch.WordTrace tailWord_1703385 prefixEnd_1703385 874655244658923232053781 := by
  unfold tailWord_1703385
  simp only [CollatzResearch.WordTrace]
  refine ⟨62127554933934534842183609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41418369955956356561455739 62127554933934534842183609)
  ·
    refine ⟨46595666200450901131637707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62127554933934534842183609 46595666200450901131637707)
    ·
      refine ⟨69893499300676351697456561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46595666200450901131637707 69893499300676351697456561)
      ·
        refine ⟨52420124475507263773092421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69893499300676351697456561 52420124475507263773092421)
        ·
          refine ⟨9828773339157611957454829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52420124475507263773092421 9828773339157611957454829)
          ·
            refine ⟨3685790002184104484045561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9828773339157611957454829 3685790002184104484045561)
            ·
              refine ⟨2764342501638078363034171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3685790002184104484045561 2764342501638078363034171)
              ·
                refine ⟨4146513752457117544551257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764342501638078363034171 4146513752457117544551257)
                ·
                  refine ⟨3109885314342838158413443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4146513752457117544551257 3109885314342838158413443)
                  ·
                    refine ⟨4664827971514257237620165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3109885314342838158413443 4664827971514257237620165)
                    ·
                      refine ⟨874655244658923232053781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4664827971514257237620165 874655244658923232053781)
                      ·
                        rfl

theorem cell23_1703385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_1703385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703385 prefixEnd_1703385 := by exact prefixLift 1703385
  have htrace : WordTrace (prefixWord ++ tailWord_1703385) baseStart_1703385 baseEnd_1703385 := by
    simpa [prefixWord, tailWord_1703385, baseEnd_1703385] using wordTrace_append hprefix tailTrace_1703385
  have hstable : (prefixWord ++ tailWord_1703385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703385).length < 2 ^ (prefixWord ++ tailWord_1703385).sum := by decide
  have hdescent : baseEnd_1703385 < baseStart_1703385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703408 : List Nat := [2, 1, 1, 1, 3, 4, 1, 4, 6]
def baseStart_1703408 : Nat := 118140960795 + 1703408 * 2 ^ 59
def prefixEnd_1703408 : Nat := 4983230072969 + 3 ^ 40 * 1703408 * 2
def baseEnd_1703408 : Nat := 97185228301552960229575

theorem tailTrace_1703408 : CollatzResearch.WordTrace tailWord_1703408 prefixEnd_1703408 97185228301552960229575 := by
  unfold tailWord_1703408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31064196906425604885135439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41418929208567473180180585 31064196906425604885135439)
  ·
    refine ⟨46596295359638407327703159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31064196906425604885135439 46596295359638407327703159)
    ·
      refine ⟨69894443039457610991554739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46596295359638407327703159 69894443039457610991554739)
      ·
        refine ⟨104841664559186416487332109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69894443039457610991554739 104841664559186416487332109)
        ·
          refine ⟨39315624209694906182749541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104841664559186416487332109 39315624209694906182749541)
          ·
            refine ⟨7371679539317794909265539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39315624209694906182749541 7371679539317794909265539)
            ·
              refine ⟨11057519308976692363898309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371679539317794909265539 11057519308976692363898309)
              ·
                refine ⟨2073284870433129818230933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11057519308976692363898309 2073284870433129818230933)
                ·
                  refine ⟨97185228301552960229575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2073284870433129818230933 97185228301552960229575)
                  ·
                    rfl

theorem cell23_1703408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_1703408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703408 prefixEnd_1703408 := by exact prefixLift 1703408
  have htrace : WordTrace (prefixWord ++ tailWord_1703408) baseStart_1703408 baseEnd_1703408 := by
    simpa [prefixWord, tailWord_1703408, baseEnd_1703408] using wordTrace_append hprefix tailTrace_1703408
  have hstable : (prefixWord ++ tailWord_1703408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703408).length < 2 ^ (prefixWord ++ tailWord_1703408).sum := by decide
  have hdescent : baseEnd_1703408 < baseStart_1703408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703498 : List Nat := [3, 1, 2, 1, 1, 3, 3, 9]
def baseStart_1703498 : Nat := 118140960795 + 1703498 * 2 ^ 59
def prefixEnd_1703498 : Nat := 4983230072969 + 3 ^ 40 * 1703498 * 2
def baseEnd_1703498 : Nat := 32396787702699307034843

theorem tailTrace_1703498 : CollatzResearch.WordTrace tailWord_1703498 prefixEnd_1703498 32396787702699307034843 := by
  unfold tailWord_1703498
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532919095631288785261787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41421117588350103427364765 15532919095631288785261787)
  ·
    refine ⟨23299378643446933177892681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15532919095631288785261787 23299378643446933177892681)
    ·
      refine ⟨17474533982585199883419511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23299378643446933177892681 17474533982585199883419511)
      ·
        refine ⟨26211800973877799825129267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17474533982585199883419511 26211800973877799825129267)
        ·
          refine ⟨39317701460816699737693901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26211800973877799825129267 39317701460816699737693901)
          ·
            refine ⟨14744138047806262401635213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39317701460816699737693901 14744138047806262401635213)
            ·
              refine ⟨5529051767927348400613205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14744138047806262401635213 5529051767927348400613205)
              ·
                refine ⟨32396787702699307034843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5529051767927348400613205 32396787702699307034843)
                ·
                  rfl

theorem cell23_1703498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 9].length) (baseStart_1703498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703498 prefixEnd_1703498 := by exact prefixLift 1703498
  have htrace : WordTrace (prefixWord ++ tailWord_1703498) baseStart_1703498 baseEnd_1703498 := by
    simpa [prefixWord, tailWord_1703498, baseEnd_1703498] using wordTrace_append hprefix tailTrace_1703498
  have hstable : (prefixWord ++ tailWord_1703498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703498).length < 2 ^ (prefixWord ++ tailWord_1703498).sum := by decide
  have hdescent : baseEnd_1703498 < baseStart_1703498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703535 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 2, 7, 2]
def baseStart_1703535 : Nat := 118140960795 + 1703535 * 2 ^ 59
def prefixEnd_1703535 : Nat := 4983230072969 + 3 ^ 40 * 1703535 * 2
def baseEnd_1703535 : Nat := 874732266757097645178091

theorem tailTrace_1703535 : CollatzResearch.WordTrace tailWord_1703535 prefixEnd_1703535 874732266757097645178091 := by
  unfold tailWord_1703535
  simp only [CollatzResearch.WordTrace]
  refine ⟨62133025883391110460144059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41422017255594073640096039 62133025883391110460144059)
  ·
    refine ⟨93199538825086665690216089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62133025883391110460144059 93199538825086665690216089)
    ·
      refine ⟨69899654118814999267662067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93199538825086665690216089 69899654118814999267662067)
      ·
        refine ⟨104849481178222498901493101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69899654118814999267662067 104849481178222498901493101)
        ·
          refine ⟨39318555441833437088059913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104849481178222498901493101 39318555441833437088059913)
          ·
            refine ⟨29488916581375077816044935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39318555441833437088059913 29488916581375077816044935)
            ·
              refine ⟨44233374872062616724067403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29488916581375077816044935 44233374872062616724067403)
              ·
                refine ⟨66350062308093925086101105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44233374872062616724067403 66350062308093925086101105)
                ·
                  refine ⟨49762546731070443814575829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66350062308093925086101105 49762546731070443814575829)
                  ·
                    refine ⟨1166309689009463526904121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49762546731070443814575829 1166309689009463526904121)
                    ·
                      refine ⟨874732266757097645178091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166309689009463526904121 874732266757097645178091)
                      ·
                        rfl

theorem cell23_1703535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 7, 2].length) (baseStart_1703535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703535 prefixEnd_1703535 := by exact prefixLift 1703535
  have htrace : WordTrace (prefixWord ++ tailWord_1703535) baseStart_1703535 baseEnd_1703535 := by
    simpa [prefixWord, tailWord_1703535, baseEnd_1703535] using wordTrace_append hprefix tailTrace_1703535
  have hstable : (prefixWord ++ tailWord_1703535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703535).length < 2 ^ (prefixWord ++ tailWord_1703535).sum := by decide
  have hdescent : baseEnd_1703535 < baseStart_1703535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703548 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_1703548 : Nat := 118140960795 + 1703548 * 2 ^ 59
def prefixEnd_1703548 : Nat := 4983230072969 + 3 ^ 40 * 1703548 * 2
def baseEnd_1703548 : Nat := 874738942005606094315531

theorem tailTrace_1703548 : CollatzResearch.WordTrace tailWord_1703548 prefixEnd_1703548 874738942005606094315531 := by
  unfold tailWord_1703548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31066750016172006840183649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41422333354896009120244865 31066750016172006840183649)
  ·
    refine ⟨23300062512129005130137737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31066750016172006840183649 23300062512129005130137737)
    ·
      refine ⟨17475046884096753847603303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23300062512129005130137737 17475046884096753847603303)
      ·
        refine ⟨26212570326145130771404955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17475046884096753847603303 26212570326145130771404955)
        ·
          refine ⟨39318855489217696157107433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26212570326145130771404955 39318855489217696157107433)
          ·
            refine ⟨29489141616913272117830575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39318855489217696157107433 29489141616913272117830575)
            ·
              refine ⟨44233712425369908176745863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29489141616913272117830575 44233712425369908176745863)
              ·
                refine ⟨66350568638054862265118795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44233712425369908176745863 66350568638054862265118795)
                ·
                  refine ⟨99525852957082293397678193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66350568638054862265118795 99525852957082293397678193)
                  ·
                    refine ⟨74644389717811720048258645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99525852957082293397678193 74644389717811720048258645)
                    ·
                      refine ⟨874738942005606094315531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 74644389717811720048258645 874738942005606094315531)
                      ·
                        rfl

theorem cell23_1703548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_1703548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703548 prefixEnd_1703548 := by exact prefixLift 1703548
  have htrace : WordTrace (prefixWord ++ tailWord_1703548) baseStart_1703548 baseEnd_1703548 := by
    simpa [prefixWord, tailWord_1703548, baseEnd_1703548] using wordTrace_append hprefix tailTrace_1703548
  have hstable : (prefixWord ++ tailWord_1703548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703548).length < 2 ^ (prefixWord ++ tailWord_1703548).sum := by decide
  have hdescent : baseEnd_1703548 < baseStart_1703548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703552 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 3, 3, 2]
def baseStart_1703552 : Nat := 118140960795 + 1703552 * 2 ^ 59
def prefixEnd_1703552 : Nat := 4983230072969 + 3 ^ 40 * 1703552 * 2
def baseEnd_1703552 : Nat := 874740995928224078665513

theorem tailTrace_1703552 : CollatzResearch.WordTrace tailWord_1703552 prefixEnd_1703552 874740995928224078665513 := by
  unfold tailWord_1703552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31066822962164761181756455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41422430616219681575675273 31066822962164761181756455)
  ·
    refine ⟨46600234443247141772634683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31066822962164761181756455 46600234443247141772634683)
    ·
      refine ⟨69900351664870712658952025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46600234443247141772634683 69900351664870712658952025)
      ·
        refine ⟨52425263748653034494214019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69900351664870712658952025 52425263748653034494214019)
        ·
          refine ⟨78637895622979551741321029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52425263748653034494214019 78637895622979551741321029)
          ·
            refine ⟨14744605429308665951497693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78637895622979551741321029 14744605429308665951497693)
            ·
              refine ⟨5529227035990749731811635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14744605429308665951497693 5529227035990749731811635)
              ·
                refine ⟨8293840553986124597717453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529227035990749731811635 8293840553986124597717453)
                ·
                  refine ⟨3110190207744796724144045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8293840553986124597717453 3110190207744796724144045)
                  ·
                    refine ⟨1166321327904298771554017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110190207744796724144045 1166321327904298771554017)
                    ·
                      refine ⟨874740995928224078665513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166321327904298771554017 874740995928224078665513)
                      ·
                        rfl

theorem cell23_1703552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_1703552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703552 prefixEnd_1703552 := by exact prefixLift 1703552
  have htrace : WordTrace (prefixWord ++ tailWord_1703552) baseStart_1703552 baseEnd_1703552 := by
    simpa [prefixWord, tailWord_1703552, baseEnd_1703552] using wordTrace_append hprefix tailTrace_1703552
  have hstable : (prefixWord ++ tailWord_1703552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703552).length < 2 ^ (prefixWord ++ tailWord_1703552).sum := by decide
  have hdescent : baseEnd_1703552 < baseStart_1703552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703582 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1703582 : Nat := 118140960795 + 1703582 * 2 ^ 59
def prefixEnd_1703582 : Nat := 4983230072969 + 3 ^ 40 * 1703582 * 2
def baseEnd_1703582 : Nat := 874756400347858961290375

theorem tailTrace_1703582 : CollatzResearch.WordTrace tailWord_1703582 prefixEnd_1703582 874756400347858961290375 := by
  unfold tailWord_1703582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766842514277604685888125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41423160076147224991403333 7766842514277604685888125)
  ·
    refine ⟨2912565942854101757208047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7766842514277604685888125 2912565942854101757208047)
    ·
      refine ⟨4368848914281152635812071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912565942854101757208047 4368848914281152635812071)
      ·
        refine ⟨6553273371421728953718107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4368848914281152635812071 6553273371421728953718107)
        ·
          refine ⟨9829910057132593430577161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553273371421728953718107 9829910057132593430577161)
          ·
            refine ⟨7372432542849445072932871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829910057132593430577161 7372432542849445072932871)
            ·
              refine ⟨11058648814274167609399307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372432542849445072932871 11058648814274167609399307)
              ·
                refine ⟨16587973221411251414098961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11058648814274167609399307 16587973221411251414098961)
                ·
                  refine ⟨12440979916058438560574221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16587973221411251414098961 12440979916058438560574221)
                  ·
                    refine ⟨4665367468521914460215333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12440979916058438560574221 4665367468521914460215333)
                    ·
                      refine ⟨874756400347858961290375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4665367468521914460215333 874756400347858961290375)
                      ·
                        rfl

theorem cell23_1703582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1703582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703582 prefixEnd_1703582 := by exact prefixLift 1703582
  have htrace : WordTrace (prefixWord ++ tailWord_1703582) baseStart_1703582 baseEnd_1703582 := by
    simpa [prefixWord, tailWord_1703582, baseEnd_1703582] using wordTrace_append hprefix tailTrace_1703582
  have hstable : (prefixWord ++ tailWord_1703582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703582).length < 2 ^ (prefixWord ++ tailWord_1703582).sum := by decide
  have hdescent : baseEnd_1703582 < baseStart_1703582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703599 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 2, 2, 2]
def baseStart_1703599 : Nat := 118140960795 + 1703599 * 2 ^ 59
def prefixEnd_1703599 : Nat := 4983230072969 + 3 ^ 40 * 1703599 * 2
def baseEnd_1703599 : Nat := 874765129518985394777797

theorem tailTrace_1703599 : CollatzResearch.WordTrace tailWord_1703599 prefixEnd_1703599 874765129518985394777797 := by
  unfold tailWord_1703599
  simp only [CollatzResearch.WordTrace]
  refine ⟨62135360155159249390473851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41423573436772832926982567 62135360155159249390473851)
  ·
    refine ⟨93203040232738874085710777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62135360155159249390473851 93203040232738874085710777)
    ·
      refine ⟨69902280174554155564283083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93203040232738874085710777 69902280174554155564283083)
      ·
        refine ⟨104853420261831233346424625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69902280174554155564283083 104853420261831233346424625)
        ·
          refine ⟨78640065196373425009818469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104853420261831233346424625 78640065196373425009818469)
          ·
            refine ⟨14745012224320017189340963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78640065196373425009818469 14745012224320017189340963)
            ·
              refine ⟨22117518336480025784011445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14745012224320017189340963 22117518336480025784011445)
              ·
                refine ⟨2073517344045002417251073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22117518336480025784011445 2073517344045002417251073)
                ·
                  refine ⟨1555138008033751812938305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2073517344045002417251073 1555138008033751812938305)
                  ·
                    refine ⟨1166353506025313859703729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1555138008033751812938305 1166353506025313859703729)
                    ·
                      refine ⟨874765129518985394777797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166353506025313859703729 874765129518985394777797)
                      ·
                        rfl

theorem cell23_1703599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 2, 2].length) (baseStart_1703599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703599 prefixEnd_1703599 := by exact prefixLift 1703599
  have htrace : WordTrace (prefixWord ++ tailWord_1703599) baseStart_1703599 baseEnd_1703599 := by
    simpa [prefixWord, tailWord_1703599, baseEnd_1703599] using wordTrace_append hprefix tailTrace_1703599
  have hstable : (prefixWord ++ tailWord_1703599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703599).length < 2 ^ (prefixWord ++ tailWord_1703599).sum := by decide
  have hdescent : baseEnd_1703599 < baseStart_1703599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703615 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 3]
def baseStart_1703615 : Nat := 118140960795 + 1703615 * 2 ^ 59
def prefixEnd_1703615 : Nat := 4983230072969 + 3 ^ 40 * 1703615 * 2
def baseEnd_1703615 : Nat := 874773345209457332177723

theorem tailTrace_1703615 : CollatzResearch.WordTrace tailWord_1703615 prefixEnd_1703615 874773345209457332177723 := by
  unfold tailWord_1703615
  simp only [CollatzResearch.WordTrace]
  refine ⟨62135943723101284123056299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41423962482067522748704199 62135943723101284123056299)
  ·
    refine ⟨93203915584651926184584449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62135943723101284123056299 93203915584651926184584449)
    ·
      refine ⟨69902936688488944638438337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93203915584651926184584449 69902936688488944638438337)
      ·
        refine ⟨52427202516366708478828753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69902936688488944638438337 52427202516366708478828753)
        ·
          refine ⟨39320401887275031359121565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52427202516366708478828753 39320401887275031359121565)
          ·
            refine ⟨14745150707728136759670587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39320401887275031359121565 14745150707728136759670587)
            ·
              refine ⟨22117726061592205139505881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14745150707728136759670587 22117726061592205139505881)
              ·
                refine ⟨16588294546194153854629411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22117726061592205139505881 16588294546194153854629411)
                ·
                  refine ⟨24882441819291230781944117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16588294546194153854629411 24882441819291230781944117)
                  ·
                    refine ⟨2332728920558552885807261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24882441819291230781944117 2332728920558552885807261)
                    ·
                      refine ⟨874773345209457332177723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2332728920558552885807261 874773345209457332177723)
                      ·
                        rfl

theorem cell23_1703615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_1703615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703615 prefixEnd_1703615 := by exact prefixLift 1703615
  have htrace : WordTrace (prefixWord ++ tailWord_1703615) baseStart_1703615 baseEnd_1703615 := by
    simpa [prefixWord, tailWord_1703615, baseEnd_1703615] using wordTrace_append hprefix tailTrace_1703615
  have hstable : (prefixWord ++ tailWord_1703615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703615).length < 2 ^ (prefixWord ++ tailWord_1703615).sum := by decide
  have hdescent : baseEnd_1703615 < baseStart_1703615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703629 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1703629 : Nat := 118140960795 + 1703629 * 2 ^ 59
def prefixEnd_1703629 : Nat := 4983230072969 + 3 ^ 40 * 1703629 * 2
def baseEnd_1703629 : Nat := 874780533938620277402659

theorem tailTrace_1703629 : CollatzResearch.WordTrace tailWord_1703629 prefixEnd_1703629 874780533938620277402659 := by
  unfold tailWord_1703629
  simp only [CollatzResearch.WordTrace]
  refine ⟨62136454345050564514065941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41424302896700376342710627 62136454345050564514065941)
  ·
    refine ⟨2912646297424245211596841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62136454345050564514065941 2912646297424245211596841)
    ·
      refine ⟨2184484723068183908697631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2912646297424245211596841 2184484723068183908697631)
      ·
        refine ⟨3276727084602275863046447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184484723068183908697631 3276727084602275863046447)
        ·
          refine ⟨4915090626903413794569671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276727084602275863046447 4915090626903413794569671)
          ·
            refine ⟨7372635940355120691854507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915090626903413794569671 7372635940355120691854507)
            ·
              refine ⟨11058953910532681037781761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372635940355120691854507 11058953910532681037781761)
              ·
                refine ⟨8294215432899510778336321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11058953910532681037781761 8294215432899510778336321)
                ·
                  refine ⟨6220661574674633083752241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294215432899510778336321 6220661574674633083752241)
                  ·
                    refine ⟨4665496181005974812814181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220661574674633083752241 4665496181005974812814181)
                    ·
                      refine ⟨874780533938620277402659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4665496181005974812814181 874780533938620277402659)
                      ·
                        rfl

theorem cell23_1703629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1703629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703629 prefixEnd_1703629 := by exact prefixLift 1703629
  have htrace : WordTrace (prefixWord ++ tailWord_1703629) baseStart_1703629 baseEnd_1703629 := by
    simpa [prefixWord, tailWord_1703629, baseEnd_1703629] using wordTrace_append hprefix tailTrace_1703629
  have hstable : (prefixWord ++ tailWord_1703629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703629).length < 2 ^ (prefixWord ++ tailWord_1703629).sum := by decide
  have hdescent : baseEnd_1703629 < baseStart_1703629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703672 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 4, 4, 2]
def baseStart_1703672 : Nat := 118140960795 + 1703672 * 2 ^ 59
def prefixEnd_1703672 : Nat := 4983230072969 + 3 ^ 40 * 1703672 * 2
def baseEnd_1703672 : Nat := 874802613606763609164961

theorem tailTrace_1703672 : CollatzResearch.WordTrace tailWord_1703672 prefixEnd_1703672 874802613606763609164961 := by
  unfold tailWord_1703672
  simp only [CollatzResearch.WordTrace]
  refine ⟨31069011341947391428940635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41425348455929855238587513 31069011341947391428940635)
  ·
    refine ⟨46603517012921087143410953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31069011341947391428940635 46603517012921087143410953)
    ·
      refine ⟨34952637759690815357558215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46603517012921087143410953 34952637759690815357558215)
      ·
        refine ⟨52428956639536223036337323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34952637759690815357558215 52428956639536223036337323)
        ·
          refine ⟨78643434959304334554505985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52428956639536223036337323 78643434959304334554505985)
          ·
            refine ⟨58982576219478250915879489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78643434959304334554505985 58982576219478250915879489)
            ·
              refine ⟨44236932164608688186909617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58982576219478250915879489 44236932164608688186909617)
              ·
                refine ⟨33177699123456516140182213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44236932164608688186909617 33177699123456516140182213)
                ·
                  refine ⟨6220818585648096776284165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33177699123456516140182213 6220818585648096776284165)
                  ·
                    refine ⟨1166403484809018145553281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220818585648096776284165 1166403484809018145553281)
                    ·
                      refine ⟨874802613606763609164961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166403484809018145553281 874802613606763609164961)
                      ·
                        rfl

theorem cell23_1703672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_1703672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703672 prefixEnd_1703672 := by exact prefixLift 1703672
  have htrace : WordTrace (prefixWord ++ tailWord_1703672) baseStart_1703672 baseEnd_1703672 := by
    simpa [prefixWord, tailWord_1703672, baseEnd_1703672] using wordTrace_append hprefix tailTrace_1703672
  have hstable : (prefixWord ++ tailWord_1703672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703672).length < 2 ^ (prefixWord ++ tailWord_1703672).sum := by decide
  have hdescent : baseEnd_1703672 < baseStart_1703672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703692 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1703692 : Nat := 118140960795 + 1703692 * 2 ^ 59
def prefixEnd_1703692 : Nat := 4983230072969 + 3 ^ 40 * 1703692 * 2
def baseEnd_1703692 : Nat := 874812883219853530914869

theorem tailTrace_1703692 : CollatzResearch.WordTrace tailWord_1703692 prefixEnd_1703692 874812883219853530914869 := by
  unfold tailWord_1703692
  simp only [CollatzResearch.WordTrace]
  refine ⟨31069376071911163136804665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41425834762548217515739553 31069376071911163136804665)
  ·
    refine ⟨23302032053933372352603499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31069376071911163136804665 23302032053933372352603499)
    ·
      refine ⟨34953048080900058528905249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23302032053933372352603499 34953048080900058528905249)
      ·
        refine ⟨26214786060675043896678937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34953048080900058528905249 26214786060675043896678937)
        ·
          refine ⟨19661089545506282922509203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26214786060675043896678937 19661089545506282922509203)
          ·
            refine ⟨29491634318259424383763805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19661089545506282922509203 29491634318259424383763805)
            ·
              refine ⟨11059362869347284143911427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29491634318259424383763805 11059362869347284143911427)
              ·
                refine ⟨16589044304020926215867141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11059362869347284143911427 16589044304020926215867141)
                ·
                  refine ⟨3110445807003923665475089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16589044304020926215867141 3110445807003923665475089)
                  ·
                    refine ⟨2332834355252942749106317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3110445807003923665475089 2332834355252942749106317)
                    ·
                      refine ⟨874812883219853530914869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2332834355252942749106317 874812883219853530914869)
                      ·
                        rfl

theorem cell23_1703692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1703692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703692 prefixEnd_1703692 := by exact prefixLift 1703692
  have htrace : WordTrace (prefixWord ++ tailWord_1703692) baseStart_1703692 baseEnd_1703692 := by
    simpa [prefixWord, tailWord_1703692, baseEnd_1703692] using wordTrace_append hprefix tailTrace_1703692
  have hstable : (prefixWord ++ tailWord_1703692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703692).length < 2 ^ (prefixWord ++ tailWord_1703692).sum := by decide
  have hdescent : baseEnd_1703692 < baseStart_1703692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703712 : List Nat := [2, 1, 1, 5, 1, 1, 3, 3, 6]
def baseStart_1703712 : Nat := 118140960795 + 1703712 * 2 ^ 59
def prefixEnd_1703712 : Nat := 4983230072969 + 3 ^ 40 * 1703712 * 2
def baseEnd_1703712 : Nat := 97202572536993716962753

theorem tailTrace_1703712 : CollatzResearch.WordTrace tailWord_1703712 prefixEnd_1703712 97202572536993716962753 := by
  unfold tailWord_1703712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31069740801874934844668695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41426321069166579792891593 31069740801874934844668695)
  ·
    refine ⟨46604611202812402267003043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31069740801874934844668695 46604611202812402267003043)
    ·
      refine ⟨69906916804218603400504565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46604611202812402267003043 69906916804218603400504565)
      ·
        refine ⟨6553773450395494068797303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69906916804218603400504565 6553773450395494068797303)
        ·
          refine ⟨9830660175593241103195955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553773450395494068797303 9830660175593241103195955)
          ·
            refine ⟨14745990263389861654793933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830660175593241103195955 14745990263389861654793933)
            ·
              refine ⟨5529746348771198120547725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14745990263389861654793933 5529746348771198120547725)
              ·
                refine ⟨2073654880789199295205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5529746348771198120547725 2073654880789199295205397)
                ·
                  refine ⟨97202572536993716962753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2073654880789199295205397 97202572536993716962753)
                  ·
                    rfl

theorem cell23_1703712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_1703712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703712 prefixEnd_1703712 := by exact prefixLift 1703712
  have htrace : WordTrace (prefixWord ++ tailWord_1703712) baseStart_1703712 baseEnd_1703712 := by
    simpa [prefixWord, tailWord_1703712, baseEnd_1703712] using wordTrace_append hprefix tailTrace_1703712
  have hstable : (prefixWord ++ tailWord_1703712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703712).length < 2 ^ (prefixWord ++ tailWord_1703712).sum := by decide
  have hdescent : baseEnd_1703712 < baseStart_1703712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703715 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1703715 : Nat := 118140960795 + 1703715 * 2 ^ 59
def prefixEnd_1703715 : Nat := 4983230072969 + 3 ^ 40 * 1703715 * 2
def baseEnd_1703715 : Nat := 874824693274906940927263

theorem tailTrace_1703715 : CollatzResearch.WordTrace tailWord_1703715 prefixEnd_1703715 874824693274906940927263 := by
  unfold tailWord_1703715
  simp only [CollatzResearch.WordTrace]
  refine ⟨62139591022739001201696599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41426394015159334134464399 62139591022739001201696599)
  ·
    refine ⟨93209386534108501802544899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62139591022739001201696599 93209386534108501802544899)
    ·
      refine ⟨139814079801162752703817349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93209386534108501802544899 139814079801162752703817349)
      ·
        refine ⟨26215139962718016131965753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139814079801162752703817349 26215139962718016131965753)
        ·
          refine ⟨19661354972038512098974315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26215139962718016131965753 19661354972038512098974315)
          ·
            refine ⟨29492032458057768148461473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19661354972038512098974315 29492032458057768148461473)
            ·
              refine ⟨22119024343543326111346105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29492032458057768148461473 22119024343543326111346105)
              ·
                refine ⟨16589268257657494583509579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22119024343543326111346105 16589268257657494583509579)
                ·
                  refine ⟨24883902386486241875264369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16589268257657494583509579 24883902386486241875264369)
                  ·
                    refine ⟨18662926789864681406448277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24883902386486241875264369 18662926789864681406448277)
                    ·
                      refine ⟨874824693274906940927263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18662926789864681406448277 874824693274906940927263)
                      ·
                        rfl

theorem cell23_1703715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1703715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703715 prefixEnd_1703715 := by exact prefixLift 1703715
  have htrace : WordTrace (prefixWord ++ tailWord_1703715) baseStart_1703715 baseEnd_1703715 := by
    simpa [prefixWord, tailWord_1703715, baseEnd_1703715] using wordTrace_append hprefix tailTrace_1703715
  have hstable : (prefixWord ++ tailWord_1703715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703715).length < 2 ^ (prefixWord ++ tailWord_1703715).sum := by decide
  have hdescent : baseEnd_1703715 < baseStart_1703715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703735 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 5]
def baseStart_1703735 : Nat := 118140960795 + 1703735 * 2 ^ 59
def prefixEnd_1703735 : Nat := 4983230072969 + 3 ^ 40 * 1703735 * 2
def baseEnd_1703735 : Nat := 874834962887996862677171

theorem tailTrace_1703735 : CollatzResearch.WordTrace tailWord_1703735 prefixEnd_1703735 874834962887996862677171 := by
  unfold tailWord_1703735
  simp only [CollatzResearch.WordTrace]
  refine ⟨62140320482666544617424659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41426880321777696411616439 62140320482666544617424659)
  ·
    refine ⟨93210480723999816926136989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62140320482666544617424659 93210480723999816926136989)
    ·
      refine ⟨34953930271499931347301371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93210480723999816926136989 34953930271499931347301371)
      ·
        refine ⟨52430895407249897020952057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34953930271499931347301371 52430895407249897020952057)
        ·
          refine ⟨39323171555437422765714043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52430895407249897020952057 39323171555437422765714043)
          ·
            refine ⟨58984757333156134148571065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39323171555437422765714043 58984757333156134148571065)
            ·
              refine ⟨44238567999867100611428299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58984757333156134148571065 44238567999867100611428299)
              ·
                refine ⟨66357851999800650917142449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44238567999867100611428299 66357851999800650917142449)
                ·
                  refine ⟨49768388999850488187856837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66357851999800650917142449 49768388999850488187856837)
                  ·
                    refine ⟨9331572937471966535223157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49768388999850488187856837 9331572937471966535223157)
                    ·
                      refine ⟨874834962887996862677171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9331572937471966535223157 874834962887996862677171)
                      ·
                        rfl

theorem cell23_1703735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_1703735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703735 prefixEnd_1703735 := by exact prefixLift 1703735
  have htrace : WordTrace (prefixWord ++ tailWord_1703735) baseStart_1703735 baseEnd_1703735 := by
    simpa [prefixWord, tailWord_1703735, baseEnd_1703735] using wordTrace_append hprefix tailTrace_1703735
  have hstable : (prefixWord ++ tailWord_1703735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703735).length < 2 ^ (prefixWord ++ tailWord_1703735).sum := by decide
  have hdescent : baseEnd_1703735 < baseStart_1703735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703749 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 2, 3, 2]
def baseStart_1703749 : Nat := 118140960795 + 1703749 * 2 ^ 59
def prefixEnd_1703749 : Nat := 4983230072969 + 3 ^ 40 * 1703749 * 2
def baseEnd_1703749 : Nat := 874842151617159807902107

theorem tailTrace_1703749 : CollatzResearch.WordTrace tailWord_1703749 prefixEnd_1703749 874842151617159807902107 := by
  unfold tailWord_1703749
  simp only [CollatzResearch.WordTrace]
  refine ⟨62140831104615825008434301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41427220736410550005622867 62140831104615825008434301)
  ·
    refine ⟨23302811664230934378162863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62140831104615825008434301 23302811664230934378162863)
    ·
      refine ⟨34954217496346401567244295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23302811664230934378162863 34954217496346401567244295)
      ·
        refine ⟨52431326244519602350866443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34954217496346401567244295 52431326244519602350866443)
        ·
          refine ⟨78646989366779403526299665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52431326244519602350866443 78646989366779403526299665)
          ·
            refine ⟨58985242025084552644724749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78646989366779403526299665 58985242025084552644724749)
            ·
              refine ⟨22119465759406707241771781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58985242025084552644724749 22119465759406707241771781)
              ·
                refine ⟨4147399829888757607832209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22119465759406707241771781 4147399829888757607832209)
                ·
                  refine ⟨3110549872416568205874157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4147399829888757607832209 3110549872416568205874157)
                  ·
                    refine ⟨1166456202156213077202809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110549872416568205874157 1166456202156213077202809)
                    ·
                      refine ⟨874842151617159807902107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166456202156213077202809 874842151617159807902107)
                      ·
                        rfl

theorem cell23_1703749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_1703749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703749 prefixEnd_1703749 := by exact prefixLift 1703749
  have htrace : WordTrace (prefixWord ++ tailWord_1703749) baseStart_1703749 baseEnd_1703749 := by
    simpa [prefixWord, tailWord_1703749, baseEnd_1703749] using wordTrace_append hprefix tailTrace_1703749
  have hstable : (prefixWord ++ tailWord_1703749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703749).length < 2 ^ (prefixWord ++ tailWord_1703749).sum := by decide
  have hdescent : baseEnd_1703749 < baseStart_1703749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703750 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_1703750 : Nat := 118140960795 + 1703750 * 2 ^ 59
def prefixEnd_1703750 : Nat := 4983230072969 + 3 ^ 40 * 1703750 * 2
def baseEnd_1703750 : Nat := 291614221699271434663201

theorem tailTrace_1703750 : CollatzResearch.WordTrace tailWord_1703750 prefixEnd_1703750 291614221699271434663201 := by
  unfold tailWord_1703750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1941902111800381318100647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41427245051741468119480469 1941902111800381318100647)
  ·
    refine ⟨2912853167700571977150971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1941902111800381318100647 2912853167700571977150971)
    ·
      refine ⟨4369279751550857965726457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2912853167700571977150971 4369279751550857965726457)
      ·
        refine ⟨3276959813663143474294843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4369279751550857965726457 3276959813663143474294843)
        ·
          refine ⟨4915439720494715211442265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276959813663143474294843 4915439720494715211442265)
          ·
            refine ⟨3686579790371036408581699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4915439720494715211442265 3686579790371036408581699)
            ·
              refine ⟨5529869685556554612872549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3686579790371036408581699 5529869685556554612872549)
              ·
                refine ⟨1036850566041853989913603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5529869685556554612872549 1036850566041853989913603)
                ·
                  refine ⟨1555275849062780984870405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036850566041853989913603 1555275849062780984870405)
                  ·
                    refine ⟨291614221699271434663201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1555275849062780984870405 291614221699271434663201)
                    ·
                      rfl

theorem cell23_1703750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_1703750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703750 prefixEnd_1703750 := by exact prefixLift 1703750
  have htrace : WordTrace (prefixWord ++ tailWord_1703750) baseStart_1703750 baseEnd_1703750 := by
    simpa [prefixWord, tailWord_1703750, baseEnd_1703750] using wordTrace_append hprefix tailTrace_1703750
  have hstable : (prefixWord ++ tailWord_1703750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703750).length < 2 ^ (prefixWord ++ tailWord_1703750).sum := by decide
  have hdescent : baseEnd_1703750 < baseStart_1703750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703785 : List Nat := [1, 2, 1, 1, 1, 3, 1, 13]
def baseStart_1703785 : Nat := 118140960795 + 1703785 * 2 ^ 59
def prefixEnd_1703785 : Nat := 4983230072969 + 3 ^ 40 * 1703785 * 2
def baseEnd_1703785 : Nat := 32402245811878580261183

theorem tailTrace_1703785 : CollatzResearch.WordTrace tailWord_1703785 prefixEnd_1703785 32402245811878580261183 := by
  unfold tailWord_1703785
  simp only [CollatzResearch.WordTrace]
  refine ⟨62142144132485403156744809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41428096088323602104496539 62142144132485403156744809)
  ·
    refine ⟨46606608099364052367558607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62142144132485403156744809 46606608099364052367558607)
    ·
      refine ⟨69909912149046078551337911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46606608099364052367558607 69909912149046078551337911)
      ·
        refine ⟨104864868223569117827006867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69909912149046078551337911 104864868223569117827006867)
        ·
          refine ⟨157297302335353676740510301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104864868223569117827006867 157297302335353676740510301)
          ·
            refine ⟨58986488375757628777691363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157297302335353676740510301 58986488375757628777691363)
            ·
              refine ⟨88479732563636443166537045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58986488375757628777691363 88479732563636443166537045)
              ·
                refine ⟨32402245811878580261183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 88479732563636443166537045 32402245811878580261183)
                ·
                  rfl

theorem cell23_1703785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 13].length) (baseStart_1703785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703785 prefixEnd_1703785 := by exact prefixLift 1703785
  have htrace : WordTrace (prefixWord ++ tailWord_1703785) baseStart_1703785 baseEnd_1703785 := by
    simpa [prefixWord, tailWord_1703785, baseEnd_1703785] using wordTrace_append hprefix tailTrace_1703785
  have hstable : (prefixWord ++ tailWord_1703785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703785).length < 2 ^ (prefixWord ++ tailWord_1703785).sum := by decide
  have hdescent : baseEnd_1703785 < baseStart_1703785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703790 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1703790 : Nat := 118140960795 + 1703790 * 2 ^ 59
def prefixEnd_1703790 : Nat := 4983230072969 + 3 ^ 40 * 1703790 * 2
def baseEnd_1703790 : Nat := 874863204323994147489419

theorem tailTrace_1703790 : CollatzResearch.WordTrace tailWord_1703790 prefixEnd_1703790 874863204323994147489419 := by
  unfold tailWord_1703790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767790812183411126334603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41428217664978192673784549 7767790812183411126334603)
  ·
    refine ⟨11651686218275116689501905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767790812183411126334603 11651686218275116689501905)
    ·
      refine ⟨8738764663706337517126429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11651686218275116689501905 8738764663706337517126429)
      ·
        refine ⟨3277036748889876568922411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8738764663706337517126429 3277036748889876568922411)
        ·
          refine ⟨4915555123334814853383617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277036748889876568922411 4915555123334814853383617)
          ·
            refine ⟨3686666342501111140037713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4915555123334814853383617 3686666342501111140037713)
            ·
              refine ⟨2764999756875833355028285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3686666342501111140037713 2764999756875833355028285)
              ·
                refine ⟨1036874908828437508135607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2764999756875833355028285 1036874908828437508135607)
                ·
                  refine ⟨1555312363242656262203411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036874908828437508135607 1555312363242656262203411)
                  ·
                    refine ⟨2332968544863984393305117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1555312363242656262203411 2332968544863984393305117)
                    ·
                      refine ⟨874863204323994147489419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2332968544863984393305117 874863204323994147489419)
                      ·
                        rfl

theorem cell23_1703790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1703790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703790 prefixEnd_1703790 := by exact prefixLift 1703790
  have htrace : WordTrace (prefixWord ++ tailWord_1703790) baseStart_1703790 baseEnd_1703790 := by
    simpa [prefixWord, tailWord_1703790, baseEnd_1703790] using wordTrace_append hprefix tailTrace_1703790
  have hstable : (prefixWord ++ tailWord_1703790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703790).length < 2 ^ (prefixWord ++ tailWord_1703790).sum := by decide
  have hdescent : baseEnd_1703790 < baseStart_1703790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703813 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 1, 2, 2]
def baseStart_1703813 : Nat := 118140960795 + 1703813 * 2 ^ 59
def prefixEnd_1703813 : Nat := 4983230072969 + 3 ^ 40 * 1703813 * 2
def baseEnd_1703813 : Nat := 874875014379047557501813

theorem tailTrace_1703813 : CollatzResearch.WordTrace tailWord_1703813 prefixEnd_1703813 874875014379047557501813 := by
  unfold tailWord_1703813
  simp only [CollatzResearch.WordTrace]
  refine ⟨62143165376383963938764093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41428776917589309292509395 62143165376383963938764093)
  ·
    refine ⟨23303687016143986477036535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62143165376383963938764093 23303687016143986477036535)
    ·
      refine ⟨34955530524215979715554803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23303687016143986477036535 34955530524215979715554803)
      ·
        refine ⟨52433295786323969573332205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34955530524215979715554803 52433295786323969573332205)
        ·
          refine ⟨19662485919871488589999577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52433295786323969573332205 19662485919871488589999577)
          ·
            refine ⟨14746864439903616442499683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19662485919871488589999577 14746864439903616442499683)
            ·
              refine ⟨22120296659855424663749525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14746864439903616442499683 22120296659855424663749525)
              ·
                refine ⟨1036888905930723031113259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22120296659855424663749525 1036888905930723031113259)
                ·
                  refine ⟨1555333358896084546669889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036888905930723031113259 1555333358896084546669889)
                  ·
                    refine ⟨1166500019172063410002417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1555333358896084546669889 1166500019172063410002417)
                    ·
                      refine ⟨874875014379047557501813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166500019172063410002417 874875014379047557501813)
                      ·
                        rfl

theorem cell23_1703813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_1703813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703813 prefixEnd_1703813 := by exact prefixLift 1703813
  have htrace : WordTrace (prefixWord ++ tailWord_1703813) baseStart_1703813 baseEnd_1703813 := by
    simpa [prefixWord, tailWord_1703813, baseEnd_1703813] using wordTrace_append hprefix tailTrace_1703813
  have hstable : (prefixWord ++ tailWord_1703813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703813).length < 2 ^ (prefixWord ++ tailWord_1703813).sum := by decide
  have hdescent : baseEnd_1703813 < baseStart_1703813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703826 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1703826 : Nat := 118140960795 + 1703826 * 2 ^ 59
def prefixEnd_1703826 : Nat := 4983230072969 + 3 ^ 40 * 1703826 * 2
def baseEnd_1703826 : Nat := 874881689627556006639253

theorem tailTrace_1703826 : CollatzResearch.WordTrace tailWord_1703826 prefixEnd_1703826 874881689627556006639253 := by
  unfold tailWord_1703826
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535909881334216789746833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41429093016891244772658221 15535909881334216789746833)
  ·
    refine ⟨11651932411000662592310125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15535909881334216789746833 11651932411000662592310125)
    ·
      refine ⟨4369474654125248472116297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11651932411000662592310125 4369474654125248472116297)
      ·
        refine ⟨3277105990593936354087223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4369474654125248472116297 3277105990593936354087223)
        ·
          refine ⟨4915658985890904531130835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277105990593936354087223 4915658985890904531130835)
          ·
            refine ⟨7373488478836356796696253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915658985890904531130835 7373488478836356796696253)
            ·
              refine ⟨2765058179563633798761095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7373488478836356796696253 2765058179563633798761095)
              ·
                refine ⟨4147587269345450698141643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765058179563633798761095 4147587269345450698141643)
                ·
                  refine ⟨6221380904018176047212465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147587269345450698141643 6221380904018176047212465)
                  ·
                    refine ⟨4666035678013632035409349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6221380904018176047212465 4666035678013632035409349)
                    ·
                      refine ⟨874881689627556006639253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4666035678013632035409349 874881689627556006639253)
                      ·
                        rfl

theorem cell23_1703826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1703826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703826 prefixEnd_1703826 := by exact prefixLift 1703826
  have htrace : WordTrace (prefixWord ++ tailWord_1703826) baseStart_1703826 baseEnd_1703826 := by
    simpa [prefixWord, tailWord_1703826, baseEnd_1703826] using wordTrace_append hprefix tailTrace_1703826
  have hstable : (prefixWord ++ tailWord_1703826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703826).length < 2 ^ (prefixWord ++ tailWord_1703826).sum := by decide
  have hdescent : baseEnd_1703826 < baseStart_1703826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703836 : List Nat := [2, 2, 3, 3, 1, 3, 2, 7]
def baseStart_1703836 : Nat := 118140960795 + 1703836 * 2 ^ 59
def prefixEnd_1703836 : Nat := 4983230072969 + 3 ^ 40 * 1703836 * 2
def baseEnd_1703836 : Nat := 32403215719781517315341

theorem tailTrace_1703836 : CollatzResearch.WordTrace tailWord_1703836 prefixEnd_1703836 32403215719781517315341 := by
  unfold tailWord_1703836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31072002127650319433425681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41429336170200425911234241 31072002127650319433425681)
  ·
    refine ⟨23304001595737739575069261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31072002127650319433425681 23304001595737739575069261)
    ·
      refine ⟨8739000598401652340650973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23304001595737739575069261 8739000598401652340650973)
      ·
        refine ⟨3277125224400619627744115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8739000598401652340650973 3277125224400619627744115)
        ·
          refine ⟨4915687836600929441616173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277125224400619627744115 4915687836600929441616173)
          ·
            refine ⟨1843382938725348540606065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4915687836600929441616173 1843382938725348540606065)
            ·
              refine ⟨1382537204044011405454549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843382938725348540606065 1382537204044011405454549)
              ·
                refine ⟨32403215719781517315341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1382537204044011405454549 32403215719781517315341)
                ·
                  rfl

theorem cell23_1703836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 2, 7].length) (baseStart_1703836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703836 prefixEnd_1703836 := by exact prefixLift 1703836
  have htrace : WordTrace (prefixWord ++ tailWord_1703836) baseStart_1703836 baseEnd_1703836 := by
    simpa [prefixWord, tailWord_1703836, baseEnd_1703836] using wordTrace_append hprefix tailTrace_1703836
  have hstable : (prefixWord ++ tailWord_1703836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703836).length < 2 ^ (prefixWord ++ tailWord_1703836).sum := by decide
  have hdescent : baseEnd_1703836 < baseStart_1703836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703847 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_1703847 : Nat := 118140960795 + 1703847 * 2 ^ 59
def prefixEnd_1703847 : Nat := 4983230072969 + 3 ^ 40 * 1703847 * 2
def baseEnd_1703847 : Nat := 874892472721300424476657

theorem tailTrace_1703847 : CollatzResearch.WordTrace tailWord_1703847 prefixEnd_1703847 874892472721300424476657 := by
  unfold tailWord_1703847
  simp only [CollatzResearch.WordTrace]
  refine ⟨62144405458260787745501795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41429603638840525163667863 62144405458260787745501795)
  ·
    refine ⟨93216608187391181618252693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62144405458260787745501795 93216608187391181618252693)
    ·
      refine ⟨4369528508783961638355595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93216608187391181618252693 4369528508783961638355595)
      ·
        refine ⟨6554292763175942457533393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369528508783961638355595 6554292763175942457533393)
        ·
          refine ⟨4915719572381956843150045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554292763175942457533393 4915719572381956843150045)
          ·
            refine ⟨1843394839643233816181267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4915719572381956843150045 1843394839643233816181267)
            ·
              refine ⟨2765092259464850724271901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843394839643233816181267 2765092259464850724271901)
              ·
                refine ⟨1036909597299319021601963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2765092259464850724271901 1036909597299319021601963)
                ·
                  refine ⟨1555364395948978532402945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1036909597299319021601963 1555364395948978532402945)
                  ·
                    refine ⟨1166523296961733899302209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1555364395948978532402945 1166523296961733899302209)
                    ·
                      refine ⟨874892472721300424476657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166523296961733899302209 874892472721300424476657)
                      ·
                        rfl

theorem cell23_1703847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_1703847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703847 prefixEnd_1703847 := by exact prefixLift 1703847
  have htrace : WordTrace (prefixWord ++ tailWord_1703847) baseStart_1703847 baseEnd_1703847 := by
    simpa [prefixWord, tailWord_1703847, baseEnd_1703847] using wordTrace_append hprefix tailTrace_1703847
  have hstable : (prefixWord ++ tailWord_1703847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703847).length < 2 ^ (prefixWord ++ tailWord_1703847).sum := by decide
  have hdescent : baseEnd_1703847 < baseStart_1703847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703872 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1703872 : Nat := 118140960795 + 1703872 * 2 ^ 59
def prefixEnd_1703872 : Nat := 4983230072969 + 3 ^ 40 * 1703872 * 2
def baseEnd_1703872 : Nat := 874905309737662826664041

theorem tailTrace_1703872 : CollatzResearch.WordTrace tailWord_1703872 prefixEnd_1703872 874905309737662826664041 := by
  unfold tailWord_1703872
  simp only [CollatzResearch.WordTrace]
  refine ⟨31072658641585108507580935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41430211522113478010107913 31072658641585108507580935)
  ·
    refine ⟨46608987962377662761371403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31072658641585108507580935 46608987962377662761371403)
    ·
      refine ⟨69913481943566494142057105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46608987962377662761371403 69913481943566494142057105)
      ·
        refine ⟨52435111457674870606542829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69913481943566494142057105 52435111457674870606542829)
        ·
          refine ⟨19663166796628076477453561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52435111457674870606542829 19663166796628076477453561)
          ·
            refine ⟨14747375097471057358090171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19663166796628076477453561 14747375097471057358090171)
            ·
              refine ⟨22121062646206586037135257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14747375097471057358090171 22121062646206586037135257)
              ·
                refine ⟨16590796984654939527851443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22121062646206586037135257 16590796984654939527851443)
                ·
                  refine ⟨24886195476982409291777165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16590796984654939527851443 24886195476982409291777165)
                  ·
                    refine ⟨9332323303868403484416437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24886195476982409291777165 9332323303868403484416437)
                    ·
                      refine ⟨874905309737662826664041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9332323303868403484416437 874905309737662826664041)
                      ·
                        rfl

theorem cell23_1703872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1703872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703872 prefixEnd_1703872 := by exact prefixLift 1703872
  have htrace : WordTrace (prefixWord ++ tailWord_1703872) baseStart_1703872 baseEnd_1703872 := by
    simpa [prefixWord, tailWord_1703872, baseEnd_1703872] using wordTrace_append hprefix tailTrace_1703872
  have hstable : (prefixWord ++ tailWord_1703872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703872).length < 2 ^ (prefixWord ++ tailWord_1703872).sum := by decide
  have hdescent : baseEnd_1703872 < baseStart_1703872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703880 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_1703880 : Nat := 118140960795 + 1703880 * 2 ^ 59
def prefixEnd_1703880 : Nat := 4983230072969 + 3 ^ 40 * 1703880 * 2
def baseEnd_1703880 : Nat := 874909417582898795364005

theorem tailTrace_1703880 : CollatzResearch.WordTrace tailWord_1703880 prefixEnd_1703880 874909417582898795364005 := by
  unfold tailWord_1703880
  simp only [CollatzResearch.WordTrace]
  refine ⟨31072804533570617190726547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41430406044760822920968729 31072804533570617190726547)
  ·
    refine ⟨46609206800355925786089821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31072804533570617190726547 46609206800355925786089821)
    ·
      refine ⟨17478452550133472169783683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46609206800355925786089821 17478452550133472169783683)
      ·
        refine ⟨26217678825200208254675525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478452550133472169783683 26217678825200208254675525)
        ·
          refine ⟨4915814779725039047751661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26217678825200208254675525 4915814779725039047751661)
          ·
            refine ⟨1843430542396889642906873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4915814779725039047751661 1843430542396889642906873)
            ·
              refine ⟨1382572906797667232180155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843430542396889642906873 1382572906797667232180155)
              ·
                refine ⟨2073859360196500848270233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382572906797667232180155 2073859360196500848270233)
                ·
                  refine ⟨1555394520147375636202675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2073859360196500848270233 1555394520147375636202675)
                  ·
                    refine ⟨2333091780221063454304013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1555394520147375636202675 2333091780221063454304013)
                    ·
                      refine ⟨874909417582898795364005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333091780221063454304013 874909417582898795364005)
                      ·
                        rfl

theorem cell23_1703880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_1703880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703880 prefixEnd_1703880 := by exact prefixLift 1703880
  have htrace : WordTrace (prefixWord ++ tailWord_1703880) baseStart_1703880 baseEnd_1703880 := by
    simpa [prefixWord, tailWord_1703880, baseEnd_1703880] using wordTrace_append hprefix tailTrace_1703880
  have hstable : (prefixWord ++ tailWord_1703880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703880).length < 2 ^ (prefixWord ++ tailWord_1703880).sum := by decide
  have hdescent : baseEnd_1703880 < baseStart_1703880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703886 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2]
def baseStart_1703886 : Nat := 118140960795 + 1703886 * 2 ^ 59
def prefixEnd_1703886 : Nat := 4983230072969 + 3 ^ 40 * 1703886 * 2
def baseEnd_1703886 : Nat := 874912498466825771888977

theorem tailTrace_1703886 : CollatzResearch.WordTrace tailWord_1703886 prefixEnd_1703886 874912498466825771888977 := by
  unfold tailWord_1703886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768228488139937175771439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41430551936746331604114341 7768228488139937175771439)
  ·
    refine ⟨11652342732209905763657159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7768228488139937175771439 11652342732209905763657159)
    ·
      refine ⟨17478514098314858645485739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11652342732209905763657159 17478514098314858645485739)
      ·
        refine ⟨26217771147472287968228609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478514098314858645485739 26217771147472287968228609)
        ·
          refine ⟨19663328360604215976171457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26217771147472287968228609 19663328360604215976171457)
          ·
            refine ⟨14747496270453161982128593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19663328360604215976171457 14747496270453161982128593)
            ·
              refine ⟨11060622202839871486596445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747496270453161982128593 11060622202839871486596445)
              ·
                refine ⟨4147733326064951807473667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11060622202839871486596445 4147733326064951807473667)
                ·
                  refine ⟨6221599989097427711210501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147733326064951807473667 6221599989097427711210501)
                  ·
                    refine ⟨1166549997955767695851969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6221599989097427711210501 1166549997955767695851969)
                    ·
                      refine ⟨874912498466825771888977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166549997955767695851969 874912498466825771888977)
                      ·
                        rfl

theorem cell23_1703886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_1703886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703886 prefixEnd_1703886 := by exact prefixLift 1703886
  have htrace : WordTrace (prefixWord ++ tailWord_1703886) baseStart_1703886 baseEnd_1703886 := by
    simpa [prefixWord, tailWord_1703886, baseEnd_1703886] using wordTrace_append hprefix tailTrace_1703886
  have hstable : (prefixWord ++ tailWord_1703886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703886).length < 2 ^ (prefixWord ++ tailWord_1703886).sum := by decide
  have hdescent : baseEnd_1703886 < baseStart_1703886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703919 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_1703919 : Nat := 118140960795 + 1703919 * 2 ^ 59
def prefixEnd_1703919 : Nat := 4983230072969 + 3 ^ 40 * 1703919 * 2
def baseEnd_1703919 : Nat := 874929443328424142776325

theorem tailTrace_1703919 : CollatzResearch.WordTrace tailWord_1703919 prefixEnd_1703919 874929443328424142776325 := by
  unfold tailWord_1703919
  simp only [CollatzResearch.WordTrace]
  refine ⟨62147031513999944042122811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41431354342666629361415207 62147031513999944042122811)
  ·
    refine ⟨93220547270999916063184217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62147031513999944042122811 93220547270999916063184217)
    ·
      refine ⟨69915410453249937047388163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93220547270999916063184217 69915410453249937047388163)
      ·
        refine ⟨104873115679874905571082245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69915410453249937047388163 104873115679874905571082245)
        ·
          refine ⟨19663709189976544794577921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104873115679874905571082245 19663709189976544794577921)
          ·
            refine ⟨14747781892482408595933441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19663709189976544794577921 14747781892482408595933441)
            ·
              refine ⟨11060836419361806446950081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747781892482408595933441 11060836419361806446950081)
              ·
                refine ⟨8295627314521354835212561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11060836419361806446950081 8295627314521354835212561)
                ·
                  refine ⟨6221720485891016126409421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8295627314521354835212561 6221720485891016126409421)
                  ·
                    refine ⟨2333145182209131047403533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6221720485891016126409421 2333145182209131047403533)
                    ·
                      refine ⟨874929443328424142776325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333145182209131047403533 874929443328424142776325)
                      ·
                        rfl

theorem cell23_1703919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_1703919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703919 prefixEnd_1703919 := by exact prefixLift 1703919
  have htrace : WordTrace (prefixWord ++ tailWord_1703919) baseStart_1703919 baseEnd_1703919 := by
    simpa [prefixWord, tailWord_1703919, baseEnd_1703919] using wordTrace_append hprefix tailTrace_1703919
  have hstable : (prefixWord ++ tailWord_1703919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703919).length < 2 ^ (prefixWord ++ tailWord_1703919).sum := by decide
  have hdescent : baseEnd_1703919 < baseStart_1703919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703952 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_1703952 : Nat := 118140960795 + 1703952 * 2 ^ 59
def prefixEnd_1703952 : Nat := 4983230072969 + 3 ^ 40 * 1703952 * 2
def baseEnd_1703952 : Nat := 291648796063340837887891

theorem tailTrace_1703952 : CollatzResearch.WordTrace tailWord_1703952 prefixEnd_1703952 291648796063340837887891 := by
  unfold tailWord_1703952
  simp only [CollatzResearch.WordTrace]
  refine ⟨31074117561440195339037055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41432156748586927118716073 31074117561440195339037055)
  ·
    refine ⟨46611176342160293008555583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31074117561440195339037055 46611176342160293008555583)
    ·
      refine ⟨69916764513240439512833375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46611176342160293008555583 69916764513240439512833375)
      ·
        refine ⟨104875146769860659269250063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69916764513240439512833375 104875146769860659269250063)
        ·
          refine ⟨157312720154790988903875095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104875146769860659269250063 157312720154790988903875095)
          ·
            refine ⟨235969080232186483355812643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157312720154790988903875095 235969080232186483355812643)
            ·
              refine ⟨353953620348279725033718965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235969080232186483355812643 353953620348279725033718965)
              ·
                refine ⟨33183151907651224221911153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353953620348279725033718965 33183151907651224221911153)
                ·
                  refine ⟨24887363930738418166433365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33183151907651224221911153 24887363930738418166433365)
                  ·
                    refine ⟨291648796063340837887891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24887363930738418166433365 291648796063340837887891)
                    ·
                      rfl

theorem cell23_1703952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_1703952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703952 prefixEnd_1703952 := by exact prefixLift 1703952
  have htrace : WordTrace (prefixWord ++ tailWord_1703952) baseStart_1703952 baseEnd_1703952 := by
    simpa [prefixWord, tailWord_1703952, baseEnd_1703952] using wordTrace_append hprefix tailTrace_1703952
  have hstable : (prefixWord ++ tailWord_1703952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703952).length < 2 ^ (prefixWord ++ tailWord_1703952).sum := by decide
  have hdescent : baseEnd_1703952 < baseStart_1703952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703986 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_1703986 : Nat := 118140960795 + 1703986 * 2 ^ 59
def prefixEnd_1703986 : Nat := 4983230072969 + 3 ^ 40 * 1703986 * 2
def baseEnd_1703986 : Nat := 291654615510758460212839

theorem tailTrace_1703986 : CollatzResearch.WordTrace tailWord_1703986 prefixEnd_1703986 291654615510758460212839 := by
  unfold tailWord_1703986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15537368801189303621202953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41432983469838142989874541 15537368801189303621202953)
  ·
    refine ⟨11653026600891977715902215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15537368801189303621202953 11653026600891977715902215)
    ·
      refine ⟨17479539901337966573853323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11653026600891977715902215 17479539901337966573853323)
      ·
        refine ⟨26219309852006949860779985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17479539901337966573853323 26219309852006949860779985)
        ·
          refine ⟨19664482389005212395584989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26219309852006949860779985 19664482389005212395584989)
          ·
            refine ⟨7374180895876954648344371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19664482389005212395584989 7374180895876954648344371)
            ·
              refine ⟨11061271343815431972516557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374180895876954648344371 11061271343815431972516557)
              ·
                refine ⟨4147976753930786989693709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11061271343815431972516557 4147976753930786989693709)
                ·
                  refine ⟨1555491282724045121135141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4147976753930786989693709 1555491282724045121135141)
                  ·
                    refine ⟨291654615510758460212839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1555491282724045121135141 291654615510758460212839)
                    ·
                      rfl

theorem cell23_1703986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_1703986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703986 prefixEnd_1703986 := by exact prefixLift 1703986
  have htrace : WordTrace (prefixWord ++ tailWord_1703986) baseStart_1703986 baseEnd_1703986 := by
    simpa [prefixWord, tailWord_1703986, baseEnd_1703986] using wordTrace_append hprefix tailTrace_1703986
  have hstable : (prefixWord ++ tailWord_1703986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703986).length < 2 ^ (prefixWord ++ tailWord_1703986).sum := by decide
  have hdescent : baseEnd_1703986 < baseStart_1703986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1703999 : List Nat := [1, 1, 2, 2, 3, 1, 2, 5, 6]
def baseStart_1703999 : Nat := 118140960795 + 1703999 * 2 ^ 59
def prefixEnd_1703999 : Nat := 4983230072969 + 3 ^ 40 * 1703999 * 2
def baseEnd_1703999 : Nat := 97218946864531536641773

theorem tailTrace_1703999 : CollatzResearch.WordTrace tailWord_1703999 prefixEnd_1703999 97218946864531536641773 := by
  unfold tailWord_1703999
  simp only [CollatzResearch.WordTrace]
  refine ⟨62149949353710117705035051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41433299569140078470023367 62149949353710117705035051)
  ·
    refine ⟨93224924030565176557552577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62149949353710117705035051 93224924030565176557552577)
    ·
      refine ⟨69918693022923882418164433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93224924030565176557552577 69918693022923882418164433)
      ·
        refine ⟨52439019767192911813623325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69918693022923882418164433 52439019767192911813623325)
        ·
          refine ⟨19664632412697341930108747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52439019767192911813623325 19664632412697341930108747)
          ·
            refine ⟨29496948619046012895163121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19664632412697341930108747 29496948619046012895163121)
            ·
              refine ⟨22122711464284509671372341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29496948619046012895163121 22122711464284509671372341)
              ·
                refine ⟨2074004199776672781691157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22122711464284509671372341 2074004199776672781691157)
                ·
                  refine ⟨97218946864531536641773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2074004199776672781691157 97218946864531536641773)
                  ·
                    rfl

theorem cell23_1703999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 6].length) (baseStart_1703999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1703999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1703999 prefixEnd_1703999 := by exact prefixLift 1703999
  have htrace : WordTrace (prefixWord ++ tailWord_1703999) baseStart_1703999 baseEnd_1703999 := by
    simpa [prefixWord, tailWord_1703999, baseEnd_1703999] using wordTrace_append hprefix tailTrace_1703999
  have hstable : (prefixWord ++ tailWord_1703999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1703999).length < 2 ^ (prefixWord ++ tailWord_1703999).sum := by decide
  have hdescent : baseEnd_1703999 < baseStart_1703999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1703999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704009 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 3]
def baseStart_1704009 : Nat := 118140960795 + 1704009 * 2 ^ 59
def prefixEnd_1704009 : Nat := 4983230072969 + 3 ^ 40 * 1704009 * 2
def baseEnd_1704009 : Nat := 874975656587328790650911

theorem tailTrace_1704009 : CollatzResearch.WordTrace tailWord_1704009 prefixEnd_1704009 874975656587328790650911 := by
  unfold tailWord_1704009
  simp only [CollatzResearch.WordTrace]
  refine ⟨62150314083673889412899081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41433542722449259608599387 62150314083673889412899081)
  ·
    refine ⟨46612735562755417059674311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62150314083673889412899081 46612735562755417059674311)
    ·
      refine ⟨69919103344133125589511467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46612735562755417059674311 69919103344133125589511467)
      ·
        refine ⟨104878655016199688384267201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69919103344133125589511467 104878655016199688384267201)
        ·
          refine ⟨78658991262149766288200401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104878655016199688384267201 78658991262149766288200401)
          ·
            refine ⟨58994243446612324716150301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78658991262149766288200401 58994243446612324716150301)
            ·
              refine ⟨22122841292479621768556363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58994243446612324716150301 22122841292479621768556363)
              ·
                refine ⟨33184261938719432652834545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22122841292479621768556363 33184261938719432652834545)
                ·
                  refine ⟨24888196454039574489625909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33184261938719432652834545 24888196454039574489625909)
                  ·
                    refine ⟨2333268417566210108402429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24888196454039574489625909 2333268417566210108402429)
                    ·
                      refine ⟨874975656587328790650911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333268417566210108402429 874975656587328790650911)
                      ·
                        rfl

theorem cell23_1704009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 5, 3].length) (baseStart_1704009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704009 prefixEnd_1704009 := by exact prefixLift 1704009
  have htrace : WordTrace (prefixWord ++ tailWord_1704009) baseStart_1704009 baseEnd_1704009 := by
    simpa [prefixWord, tailWord_1704009, baseEnd_1704009] using wordTrace_append hprefix tailTrace_1704009
  have hstable : (prefixWord ++ tailWord_1704009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704009).length < 2 ^ (prefixWord ++ tailWord_1704009).sum := by decide
  have hdescent : baseEnd_1704009 < baseStart_1704009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704013 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1704013 : Nat := 118140960795 + 1704013 * 2 ^ 59
def prefixEnd_1704013 : Nat := 4983230072969 + 3 ^ 40 * 1704013 * 2
def baseEnd_1704013 : Nat := 874977710509946775000893

theorem tailTrace_1704013 : CollatzResearch.WordTrace tailWord_1704013 prefixEnd_1704013 874977710509946775000893 := by
  unfold tailWord_1704013
  simp only [CollatzResearch.WordTrace]
  refine ⟨62150459975659398096044693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41433639983772932064029795 62150459975659398096044693)
  ·
    refine ⟨2913302811359034285752095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62150459975659398096044693 2913302811359034285752095)
    ·
      refine ⟨4369954217038551428628143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2913302811359034285752095 4369954217038551428628143)
      ·
        refine ⟨6554931325557827142942215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369954217038551428628143 6554931325557827142942215)
        ·
          refine ⟨9832396988336740714413323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6554931325557827142942215 9832396988336740714413323)
          ·
            refine ⟨14748595482505111071619985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9832396988336740714413323 14748595482505111071619985)
            ·
              refine ⟨11061446611878833303714989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14748595482505111071619985 11061446611878833303714989)
              ·
                refine ⟨4148042479454562488893121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11061446611878833303714989 4148042479454562488893121)
                ·
                  refine ⟨3111031859590921866669841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148042479454562488893121 3111031859590921866669841)
                  ·
                    refine ⟨2333273894693191400002381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3111031859590921866669841 2333273894693191400002381)
                    ·
                      refine ⟨874977710509946775000893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333273894693191400002381 874977710509946775000893)
                      ·
                        rfl

theorem cell23_1704013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1704013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704013 prefixEnd_1704013 := by exact prefixLift 1704013
  have htrace : WordTrace (prefixWord ++ tailWord_1704013) baseStart_1704013 baseEnd_1704013 := by
    simpa [prefixWord, tailWord_1704013, baseEnd_1704013] using wordTrace_append hprefix tailTrace_1704013
  have hstable : (prefixWord ++ tailWord_1704013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704013).length < 2 ^ (prefixWord ++ tailWord_1704013).sum := by decide
  have hdescent : baseEnd_1704013 < baseStart_1704013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704046 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1704046 : Nat := 118140960795 + 1704046 * 2 ^ 59
def prefixEnd_1704046 : Nat := 4983230072969 + 3 ^ 40 * 1704046 * 2
def baseEnd_1704046 : Nat := 291664885123848381962747

theorem tailTrace_1704046 : CollatzResearch.WordTrace tailWord_1704046 prefixEnd_1704046 291664885123848381962747 := by
  unfold tailWord_1704046
  simp only [CollatzResearch.WordTrace]
  refine ⟨7768957948067480591499499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41434442389693229821330661 7768957948067480591499499)
  ·
    refine ⟨11653436922101220887249249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7768957948067480591499499 11653436922101220887249249)
    ·
      refine ⟨8740077691575915665436937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11653436922101220887249249 8740077691575915665436937)
      ·
        refine ⟨6555058268681936749077703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8740077691575915665436937 6555058268681936749077703)
        ·
          refine ⟨9832587403022905123616555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555058268681936749077703 9832587403022905123616555)
          ·
            refine ⟨14748881104534357685424833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9832587403022905123616555 14748881104534357685424833)
            ·
              refine ⟨11061660828400768264068625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14748881104534357685424833 11061660828400768264068625)
              ·
                refine ⟨8296245621300576198051469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11061660828400768264068625 8296245621300576198051469)
                ·
                  refine ⟨3111092107987716074269301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8296245621300576198051469 3111092107987716074269301)
                  ·
                    refine ⟨291664885123848381962747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3111092107987716074269301 291664885123848381962747)
                    ·
                      rfl

theorem cell23_1704046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1704046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704046 prefixEnd_1704046 := by exact prefixLift 1704046
  have htrace : WordTrace (prefixWord ++ tailWord_1704046) baseStart_1704046 baseEnd_1704046 := by
    simpa [prefixWord, tailWord_1704046, baseEnd_1704046] using wordTrace_append hprefix tailTrace_1704046
  have hstable : (prefixWord ++ tailWord_1704046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704046).length < 2 ^ (prefixWord ++ tailWord_1704046).sum := by decide
  have hdescent : baseEnd_1704046 < baseStart_1704046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704093 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1704093 : Nat := 118140960795 + 1704093 * 2 ^ 59
def prefixEnd_1704093 : Nat := 4983230072969 + 3 ^ 40 * 1704093 * 2
def baseEnd_1704093 : Nat := 291672929654102154000175

theorem tailTrace_1704093 : CollatzResearch.WordTrace tailWord_1704093 prefixEnd_1704093 291672929654102154000175 := by
  unfold tailWord_1704093
  simp only [CollatzResearch.WordTrace]
  refine ⟨62153377815369571758956933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41435585210246381172637955 62153377815369571758956933)
  ·
    refine ⟨11653758340381794704804425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62153377815369571758956933 11653758340381794704804425)
    ·
      refine ⟨8740318755286346028603319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11653758340381794704804425 8740318755286346028603319)
      ·
        refine ⟨13110478132929519042904979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8740318755286346028603319 13110478132929519042904979)
        ·
          refine ⟨19665717199394278564357469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13110478132929519042904979 19665717199394278564357469)
          ·
            refine ⟨7374643949772854461634051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19665717199394278564357469 7374643949772854461634051)
            ·
              refine ⟨11061965924659281692451077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374643949772854461634051 11061965924659281692451077)
              ·
                refine ⟨2074118610873615317334577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11061965924659281692451077 2074118610873615317334577)
                ·
                  refine ⟨1555588958155211488000933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2074118610873615317334577 1555588958155211488000933)
                  ·
                    refine ⟨291672929654102154000175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1555588958155211488000933 291672929654102154000175)
                    ·
                      rfl

theorem cell23_1704093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1704093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704093 prefixEnd_1704093 := by exact prefixLift 1704093
  have htrace : WordTrace (prefixWord ++ tailWord_1704093) baseStart_1704093 baseEnd_1704093 := by
    simpa [prefixWord, tailWord_1704093, baseEnd_1704093] using wordTrace_append hprefix tailTrace_1704093
  have hstable : (prefixWord ++ tailWord_1704093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704093).length < 2 ^ (prefixWord ++ tailWord_1704093).sum := by decide
  have hdescent : baseEnd_1704093 < baseStart_1704093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704094 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1704094 : Nat := 118140960795 + 1704094 * 2 ^ 59
def prefixEnd_1704094 : Nat := 4983230072969 + 3 ^ 40 * 1704094 * 2
def baseEnd_1704094 : Nat := 875019302442960958088021

theorem tailTrace_1704094 : CollatzResearch.WordTrace tailWord_1704094 prefixEnd_1704094 875019302442960958088021 := by
  unfold tailWord_1704094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769176786045743616217917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41435609525577299286495557 7769176786045743616217917)
  ·
    refine ⟨2913441294767153856081719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7769176786045743616217917 2913441294767153856081719)
    ·
      refine ⟨4370161942150730784122579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2913441294767153856081719 4370161942150730784122579)
      ·
        refine ⟨6555242913226096176183869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370161942150730784122579 6555242913226096176183869)
        ·
          refine ⟨2458216092459786066068951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6555242913226096176183869 2458216092459786066068951)
          ·
            refine ⟨3687324138689679099103427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458216092459786066068951 3687324138689679099103427)
            ·
              refine ⟨5530986208034518648655141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687324138689679099103427 5530986208034518648655141)
              ·
                refine ⟨1037059914006472246622839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5530986208034518648655141 1037059914006472246622839)
                ·
                  refine ⟨1555589871009708369934259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037059914006472246622839 1555589871009708369934259)
                  ·
                    refine ⟨2333384806514562554901389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1555589871009708369934259 2333384806514562554901389)
                    ·
                      refine ⟨875019302442960958088021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333384806514562554901389 875019302442960958088021)
                      ·
                        rfl

theorem cell23_1704094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1704094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704094 prefixEnd_1704094 := by exact prefixLift 1704094
  have htrace : WordTrace (prefixWord ++ tailWord_1704094) baseStart_1704094 baseEnd_1704094 := by
    simpa [prefixWord, tailWord_1704094, baseEnd_1704094] using wordTrace_append hprefix tailTrace_1704094
  have hstable : (prefixWord ++ tailWord_1704094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704094).length < 2 ^ (prefixWord ++ tailWord_1704094).sum := by decide
  have hdescent : baseEnd_1704094 < baseStart_1704094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704176 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_1704176 : Nat := 118140960795 + 1704176 * 2 ^ 59
def prefixEnd_1704176 : Nat := 4983230072969 + 3 ^ 40 * 1704176 * 2
def baseEnd_1704176 : Nat := 875061407856629637262643

theorem tailTrace_1704176 : CollatzResearch.WordTrace tailWord_1704176 prefixEnd_1704176 875061407856629637262643 := by
  unfold tailWord_1704176
  simp only [CollatzResearch.WordTrace]
  refine ⟨31078202537034438467114191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41437603382712584622818921 31078202537034438467114191)
  ·
    refine ⟨46617303805551657700671287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31078202537034438467114191 46617303805551657700671287)
    ·
      refine ⟨69925955708327486551006931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46617303805551657700671287 69925955708327486551006931)
      ·
        refine ⟨104888933562491229826510397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69925955708327486551006931 104888933562491229826510397)
        ·
          refine ⟨39333350085934211184941399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104888933562491229826510397 39333350085934211184941399)
          ·
            refine ⟨59000025128901316777412099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39333350085934211184941399 59000025128901316777412099)
            ·
              refine ⟨88500037693351975166118149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59000025128901316777412099 88500037693351975166118149)
              ·
                refine ⟨16593757067503495343647153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88500037693351975166118149 16593757067503495343647153)
                ·
                  refine ⟨12445317800627621507735365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16593757067503495343647153 12445317800627621507735365)
                  ·
                    refine ⟨2333497087617679032700381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12445317800627621507735365 2333497087617679032700381)
                    ·
                      refine ⟨875061407856629637262643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333497087617679032700381 875061407856629637262643)
                      ·
                        rfl

theorem cell23_1704176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_1704176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704176 prefixEnd_1704176 := by exact prefixLift 1704176
  have htrace : WordTrace (prefixWord ++ tailWord_1704176) baseStart_1704176 baseEnd_1704176 := by
    simpa [prefixWord, tailWord_1704176, baseEnd_1704176] using wordTrace_append hprefix tailTrace_1704176
  have hstable : (prefixWord ++ tailWord_1704176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704176).length < 2 ^ (prefixWord ++ tailWord_1704176).sum := by decide
  have hdescent : baseEnd_1704176 < baseStart_1704176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704190 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1704190 : Nat := 118140960795 + 1704190 * 2 ^ 59
def prefixEnd_1704190 : Nat := 4983230072969 + 3 ^ 40 * 1704190 * 2
def baseEnd_1704190 : Nat := 875068596585792582487579

theorem tailTrace_1704190 : CollatzResearch.WordTrace tailWord_1704190 prefixEnd_1704190 875068596585792582487579 := by
  unfold tailWord_1704190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769614462002269665654753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41437943797345438216825349 7769614462002269665654753)
  ·
    refine ⟨5827210846501702249241065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7769614462002269665654753 5827210846501702249241065)
    ·
      refine ⟨4370408134876276686930799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5827210846501702249241065 4370408134876276686930799)
      ·
        refine ⟨6555612202314415030396199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370408134876276686930799 6555612202314415030396199)
        ·
          refine ⟨9833418303471622545594299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555612202314415030396199 9833418303471622545594299)
          ·
            refine ⟨14750127455207433818391449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9833418303471622545594299 14750127455207433818391449)
            ·
              refine ⟨11062595591405575363793587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14750127455207433818391449 11062595591405575363793587)
              ·
                refine ⟨16593893387108363045690381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11062595591405575363793587 16593893387108363045690381)
                ·
                  refine ⟨6222710020165636142133893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16593893387108363045690381 6222710020165636142133893)
                  ·
                    refine ⟨1166758128781056776650105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6222710020165636142133893 1166758128781056776650105)
                    ·
                      refine ⟨875068596585792582487579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166758128781056776650105 875068596585792582487579)
                      ·
                        rfl

theorem cell23_1704190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1704190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704190 prefixEnd_1704190 := by exact prefixLift 1704190
  have htrace : WordTrace (prefixWord ++ tailWord_1704190) baseStart_1704190 baseEnd_1704190 := by
    simpa [prefixWord, tailWord_1704190, baseEnd_1704190] using wordTrace_append hprefix tailTrace_1704190
  have hstable : (prefixWord ++ tailWord_1704190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704190).length < 2 ^ (prefixWord ++ tailWord_1704190).sum := by decide
  have hdescent : baseEnd_1704190 < baseStart_1704190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704206 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1704206 : Nat := 118140960795 + 1704206 * 2 ^ 59
def prefixEnd_1704206 : Nat := 4983230072969 + 3 ^ 40 * 1704206 * 2
def baseEnd_1704206 : Nat := 875076812276264519887505

theorem tailTrace_1704206 : CollatzResearch.WordTrace tailWord_1704206 prefixEnd_1704206 875076812276264519887505 := by
  unfold tailWord_1704206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769687407995024007227559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41438332842640128038546981 7769687407995024007227559)
  ·
    refine ⟨11654531111992536010841339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7769687407995024007227559 11654531111992536010841339)
    ·
      refine ⟨17481796667988804016262009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654531111992536010841339 17481796667988804016262009)
      ·
        refine ⟨13111347500991603012196507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17481796667988804016262009 13111347500991603012196507)
        ·
          refine ⟨19667021251487404518294761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13111347500991603012196507 19667021251487404518294761)
          ·
            refine ⟨14750265938615553388721071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19667021251487404518294761 14750265938615553388721071)
            ·
              refine ⟨22125398907923330083081607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14750265938615553388721071 22125398907923330083081607)
              ·
                refine ⟨33188098361884995124622411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22125398907923330083081607 33188098361884995124622411)
                ·
                  refine ⟨49782147542827492686933617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33188098361884995124622411 49782147542827492686933617)
                  ·
                    refine ⟨37336610657120619515200213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49782147542827492686933617 37336610657120619515200213)
                    ·
                      refine ⟨875076812276264519887505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37336610657120619515200213 875076812276264519887505)
                      ·
                        rfl

theorem cell23_1704206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1704206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704206 prefixEnd_1704206 := by exact prefixLift 1704206
  have htrace : WordTrace (prefixWord ++ tailWord_1704206) baseStart_1704206 baseEnd_1704206 := by
    simpa [prefixWord, tailWord_1704206, baseEnd_1704206] using wordTrace_append hprefix tailTrace_1704206
  have hstable : (prefixWord ++ tailWord_1704206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704206).length < 2 ^ (prefixWord ++ tailWord_1704206).sum := by decide
  have hdescent : baseEnd_1704206 < baseStart_1704206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704213 : List Nat := [1, 3, 2, 1, 2, 1, 2, 6, 5]
def baseStart_1704213 : Nat := 118140960795 + 1704213 * 2 ^ 59
def prefixEnd_1704213 : Nat := 4983230072969 + 3 ^ 40 * 1704213 * 2
def baseEnd_1704213 : Nat := 97231156293427332499997

theorem tailTrace_1704213 : CollatzResearch.WordTrace tailWord_1704213 prefixEnd_1704213 97231156293427332499997 := by
  unfold tailWord_1704213
  simp only [CollatzResearch.WordTrace]
  refine ⟨62157754574934832253325293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41438503049956554835550195 62157754574934832253325293)
  ·
    refine ⟨23309157965600562094996985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62157754574934832253325293 23309157965600562094996985)
    ·
      refine ⟨17481868474200421571247739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23309157965600562094996985 17481868474200421571247739)
      ·
        refine ⟨26222802711300632356871609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17481868474200421571247739 26222802711300632356871609)
        ·
          refine ⟨19667102033475474267653707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26222802711300632356871609 19667102033475474267653707)
          ·
            refine ⟨29500653050213211401480561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19667102033475474267653707 29500653050213211401480561)
            ·
              refine ⟨22125489787659908551110421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29500653050213211401480561 22125489787659908551110421)
              ·
                refine ⟨1037132333796558213333301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22125489787659908551110421 1037132333796558213333301)
                ·
                  refine ⟨97231156293427332499997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037132333796558213333301 97231156293427332499997)
                  ·
                    rfl

theorem cell23_1704213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_1704213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704213 prefixEnd_1704213 := by exact prefixLift 1704213
  have htrace : WordTrace (prefixWord ++ tailWord_1704213) baseStart_1704213 baseEnd_1704213 := by
    simpa [prefixWord, tailWord_1704213, baseEnd_1704213] using wordTrace_append hprefix tailTrace_1704213
  have hstable : (prefixWord ++ tailWord_1704213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704213).length < 2 ^ (prefixWord ++ tailWord_1704213).sum := by decide
  have hdescent : baseEnd_1704213 < baseStart_1704213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704224 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 2, 2, 2]
def baseStart_1704224 : Nat := 118140960795 + 1704224 * 2 ^ 59
def prefixEnd_1704224 : Nat := 4983230072969 + 3 ^ 40 * 1704224 * 2
def baseEnd_1704224 : Nat := 875086054928045449462423

theorem tailTrace_1704224 : CollatzResearch.WordTrace tailWord_1704224 prefixEnd_1704224 875086054928045449462423 := by
  unfold tailWord_1704224
  simp only [CollatzResearch.WordTrace]
  refine ⟨31079077888947490565987863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41438770518596654087983817 31079077888947490565987863)
  ·
    refine ⟨46618616833421235848981795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31079077888947490565987863 46618616833421235848981795)
    ·
      refine ⟨69927925250131853773472693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46618616833421235848981795 69927925250131853773472693)
      ·
        refine ⟨6555742992199861291263065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69927925250131853773472693 6555742992199861291263065)
        ·
          refine ⟨4916807244149895968447299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6555742992199861291263065 4916807244149895968447299)
          ·
            refine ⟨7375210866224843952670949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916807244149895968447299 7375210866224843952670949)
            ·
              refine ⟨1382852037417158241125803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7375210866224843952670949 1382852037417158241125803)
              ·
                refine ⟨2074278056125737361688705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382852037417158241125803 2074278056125737361688705)
                ·
                  refine ⟨1555708542094303021266529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2074278056125737361688705 1555708542094303021266529)
                  ·
                    refine ⟨1166781406570727265949897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1555708542094303021266529 1166781406570727265949897)
                    ·
                      refine ⟨875086054928045449462423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166781406570727265949897 875086054928045449462423)
                      ·
                        rfl

theorem cell23_1704224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_1704224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704224 prefixEnd_1704224 := by exact prefixLift 1704224
  have htrace : WordTrace (prefixWord ++ tailWord_1704224) baseStart_1704224 baseEnd_1704224 := by
    simpa [prefixWord, tailWord_1704224, baseEnd_1704224] using wordTrace_append hprefix tailTrace_1704224
  have hstable : (prefixWord ++ tailWord_1704224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704224).length < 2 ^ (prefixWord ++ tailWord_1704224).sum := by decide
  have hdescent : baseEnd_1704224 < baseStart_1704224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704243 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 2, 5]
def baseStart_1704243 : Nat := 118140960795 + 1704243 * 2 ^ 59
def prefixEnd_1704243 : Nat := 4983230072969 + 3 ^ 40 * 1704243 * 2
def baseEnd_1704243 : Nat := 291698603686826958374945

theorem tailTrace_1704243 : CollatzResearch.WordTrace tailWord_1704243 prefixEnd_1704243 291698603686826958374945 := by
  unfold tailWord_1704243
  simp only [CollatzResearch.WordTrace]
  refine ⟨62158848764826147376917383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41439232509884098251278255 62158848764826147376917383)
  ·
    refine ⟨93238273147239221065376075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62158848764826147376917383 93238273147239221065376075)
    ·
      refine ⟨139857409720858831598064113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93238273147239221065376075 139857409720858831598064113)
      ·
        refine ⟨104893057290644123698548085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139857409720858831598064113 104893057290644123698548085)
        ·
          refine ⟨9833724120997886596738883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104893057290644123698548085 9833724120997886596738883)
          ·
            refine ⟨14750586181496829895108325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9833724120997886596738883 14750586181496829895108325)
            ·
              refine ⟨2765734909030655605332811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14750586181496829895108325 2765734909030655605332811)
              ·
                refine ⟨4148602363545983407999217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765734909030655605332811 4148602363545983407999217)
                ·
                  refine ⟨3111451772659487555999413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148602363545983407999217 3111451772659487555999413)
                  ·
                    refine ⟨291698603686826958374945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3111451772659487555999413 291698603686826958374945)
                    ·
                      rfl

theorem cell23_1704243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 5].length) (baseStart_1704243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704243 prefixEnd_1704243 := by exact prefixLift 1704243
  have htrace : WordTrace (prefixWord ++ tailWord_1704243) baseStart_1704243 baseEnd_1704243 := by
    simpa [prefixWord, tailWord_1704243, baseEnd_1704243] using wordTrace_append hprefix tailTrace_1704243
  have hstable : (prefixWord ++ tailWord_1704243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704243).length < 2 ^ (prefixWord ++ tailWord_1704243).sum := by decide
  have hdescent : baseEnd_1704243 < baseStart_1704243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704263 : List Nat := [1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1704263 : Nat := 118140960795 + 1704263 * 2 ^ 59
def prefixEnd_1704263 : Nat := 4983230072969 + 3 ^ 40 * 1704263 * 2
def baseEnd_1704263 : Nat := 875106080673570796874743

theorem tailTrace_1704263 : CollatzResearch.WordTrace tailWord_1704263 prefixEnd_1704263 875106080673570796874743 := by
  unfold tailWord_1704263
  simp only [CollatzResearch.WordTrace]
  refine ⟨62159578224753690792645443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41439718816502460528430295 62159578224753690792645443)
  ·
    refine ⟨93239367337130536188968165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62159578224753690792645443 93239367337130536188968165)
    ·
      refine ⟨17482381375711975535431531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93239367337130536188968165 17482381375711975535431531)
      ·
        refine ⟨26223572063567963303147297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17482381375711975535431531 26223572063567963303147297)
        ·
          refine ⟨19667679047675972477360473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26223572063567963303147297 19667679047675972477360473)
          ·
            refine ⟨14750759285756979358020355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19667679047675972477360473 14750759285756979358020355)
            ·
              refine ⟨22126138928635469037030533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14750759285756979358020355 22126138928635469037030533)
              ·
                refine ⟨4148651049119150444443225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22126138928635469037030533 4148651049119150444443225)
                ·
                  refine ⟨3111488286839362833332419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148651049119150444443225 3111488286839362833332419)
                  ·
                    refine ⟨4667232430259044249998629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111488286839362833332419 4667232430259044249998629)
                    ·
                      refine ⟨875106080673570796874743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4667232430259044249998629 875106080673570796874743)
                      ·
                        rfl

theorem cell23_1704263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1704263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704263 prefixEnd_1704263 := by exact prefixLift 1704263
  have htrace : WordTrace (prefixWord ++ tailWord_1704263) baseStart_1704263 baseEnd_1704263 := by
    simpa [prefixWord, tailWord_1704263, baseEnd_1704263] using wordTrace_append hprefix tailTrace_1704263
  have hstable : (prefixWord ++ tailWord_1704263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704263).length < 2 ^ (prefixWord ++ tailWord_1704263).sum := by decide
  have hdescent : baseEnd_1704263 < baseStart_1704263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704290 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1704290 : Nat := 118140960795 + 1704290 * 2 ^ 59
def prefixEnd_1704290 : Nat := 4983230072969 + 3 ^ 40 * 1704290 * 2
def baseEnd_1704290 : Nat := 291706648217080730412373

theorem tailTrace_1704290 : CollatzResearch.WordTrace tailWord_1704290 prefixEnd_1704290 291706648217080730412373 := by
  unfold tailWord_1704290
  simp only [CollatzResearch.WordTrace]
  refine ⟨15540140748913968600969581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41440375330437249602585549 15540140748913968600969581)
  ·
    refine ⟨5827552780842738225363593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15540140748913968600969581 5827552780842738225363593)
    ·
      refine ⟨4370664585632053669022695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5827552780842738225363593 4370664585632053669022695)
      ·
        refine ⟨6555996878448080503534043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4370664585632053669022695 6555996878448080503534043)
        ·
          refine ⟨9833995317672120755301065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6555996878448080503534043 9833995317672120755301065)
          ·
            refine ⟨7375496488254090566475799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9833995317672120755301065 7375496488254090566475799)
            ·
              refine ⟨11063244732381135849713699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7375496488254090566475799 11063244732381135849713699)
              ·
                refine ⟨16594867098571703774570549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11063244732381135849713699 16594867098571703774570549)
                ·
                  refine ⟨1555768790491097228865989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16594867098571703774570549 1555768790491097228865989)
                  ·
                    refine ⟨291706648217080730412373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1555768790491097228865989 291706648217080730412373)
                    ·
                      rfl

theorem cell23_1704290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1704290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704290 prefixEnd_1704290 := by exact prefixLift 1704290
  have htrace : WordTrace (prefixWord ++ tailWord_1704290) baseStart_1704290 baseEnd_1704290 := by
    simpa [prefixWord, tailWord_1704290, baseEnd_1704290] using wordTrace_append hprefix tailTrace_1704290
  have hstable : (prefixWord ++ tailWord_1704290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704290).length < 2 ^ (prefixWord ++ tailWord_1704290).sum := by decide
  have hdescent : baseEnd_1704290 < baseStart_1704290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704300 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 3]
def baseStart_1704300 : Nat := 118140960795 + 1704300 * 2 ^ 59
def prefixEnd_1704300 : Nat := 4983230072969 + 3 ^ 40 * 1704300 * 2
def baseEnd_1704300 : Nat := 875125079457787152112073

theorem tailTrace_1704300 : CollatzResearch.WordTrace tailWord_1704300 prefixEnd_1704300 875125079457787152112073 := by
  unfold tailWord_1704300
  simp only [CollatzResearch.WordTrace]
  refine ⟨31080463862809823055871177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41440618483746430741161569 31080463862809823055871177)
  ·
    refine ⟨23310347897107367291903383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31080463862809823055871177 23310347897107367291903383)
    ·
      refine ⟨34965521845661050937855075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23310347897107367291903383 34965521845661050937855075)
      ·
        refine ⟨52448282768491576406782613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34965521845661050937855075 52448282768491576406782613)
        ·
          refine ⟨2458513254773042644067935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52448282768491576406782613 2458513254773042644067935)
          ·
            refine ⟨3687769882159563966101903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458513254773042644067935 3687769882159563966101903)
            ·
              refine ⟨5531654823239345949152855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687769882159563966101903 5531654823239345949152855)
              ·
                refine ⟨8297482234859018923729283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531654823239345949152855 8297482234859018923729283)
                ·
                  refine ⟨12446223352288528385593925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297482234859018923729283 12446223352288528385593925)
                  ·
                    refine ⟨2333666878554099072298861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12446223352288528385593925 2333666878554099072298861)
                    ·
                      refine ⟨875125079457787152112073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333666878554099072298861 875125079457787152112073)
                      ·
                        rfl

theorem cell23_1704300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_1704300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704300 prefixEnd_1704300 := by exact prefixLift 1704300
  have htrace : WordTrace (prefixWord ++ tailWord_1704300) baseStart_1704300 baseEnd_1704300 := by
    simpa [prefixWord, tailWord_1704300, baseEnd_1704300] using wordTrace_append hprefix tailTrace_1704300
  have hstable : (prefixWord ++ tailWord_1704300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704300).length < 2 ^ (prefixWord ++ tailWord_1704300).sum := by decide
  have hdescent : baseEnd_1704300 < baseStart_1704300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704336 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_1704336 : Nat := 118140960795 + 1704336 * 2 ^ 59
def prefixEnd_1704336 : Nat := 4983230072969 + 3 ^ 40 * 1704336 * 2
def baseEnd_1704336 : Nat := 875143564761349011261907

theorem tailTrace_1704336 : CollatzResearch.WordTrace tailWord_1704336 prefixEnd_1704336 875143564761349011261907 := by
  unfold tailWord_1704336
  simp only [CollatzResearch.WordTrace]
  refine ⟨31081120376744612130026431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41441493835659482840035241 31081120376744612130026431)
  ·
    refine ⟨46621680565116918195039647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31081120376744612130026431 46621680565116918195039647)
    ·
      refine ⟨69932520847675377292559471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46621680565116918195039647 69932520847675377292559471)
      ·
        refine ⟨104898781271513065938839207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69932520847675377292559471 104898781271513065938839207)
        ·
          refine ⟨157348171907269598908258811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104898781271513065938839207 157348171907269598908258811)
          ·
            refine ⟨236022257860904398362388217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157348171907269598908258811 236022257860904398362388217)
            ·
              refine ⟨177016693395678298771791163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236022257860904398362388217 177016693395678298771791163)
              ·
                refine ⟨265525040093517448157686745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177016693395678298771791163 265525040093517448157686745)
                ·
                  refine ⟨199143780070138086118265059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265525040093517448157686745 199143780070138086118265059)
                  ·
                    refine ⟨298715670105207129177397589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199143780070138086118265059 298715670105207129177397589)
                    ·
                      refine ⟨875143564761349011261907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 298715670105207129177397589 875143564761349011261907)
                      ·
                        rfl

theorem cell23_1704336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_1704336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704336 prefixEnd_1704336 := by exact prefixLift 1704336
  have htrace : WordTrace (prefixWord ++ tailWord_1704336) baseStart_1704336 baseEnd_1704336 := by
    simpa [prefixWord, tailWord_1704336, baseEnd_1704336] using wordTrace_append hprefix tailTrace_1704336
  have hstable : (prefixWord ++ tailWord_1704336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704336).length < 2 ^ (prefixWord ++ tailWord_1704336).sum := by decide
  have hdescent : baseEnd_1704336 < baseStart_1704336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704370 : List Nat := [3, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_1704370 : Nat := 118140960795 + 1704370 * 2 ^ 59
def prefixEnd_1704370 : Nat := 4983230072969 + 3 ^ 40 * 1704370 * 2
def baseEnd_1704370 : Nat := 875161023103601878236751

theorem tailTrace_1704370 : CollatzResearch.WordTrace tailWord_1704370 prefixEnd_1704370 875161023103601878236751 := by
  unfold tailWord_1704370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15540870208841512016697641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41442320556910698711193709 15540870208841512016697641)
  ·
    refine ⟨11655652656631134012523231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15540870208841512016697641 11655652656631134012523231)
    ·
      refine ⟨17483478984946701018784847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11655652656631134012523231 17483478984946701018784847)
      ·
        refine ⟨26225218477420051528177271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17483478984946701018784847 26225218477420051528177271)
        ·
          refine ⟨39337827716130077292265907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26225218477420051528177271 39337827716130077292265907)
          ·
            refine ⟨59006741574195115938398861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39337827716130077292265907 59006741574195115938398861)
            ·
              refine ⟨22127528090323168476899573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59006741574195115938398861 22127528090323168476899573)
              ·
                refine ⟨2074455758467797044709335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22127528090323168476899573 2074455758467797044709335)
                ·
                  refine ⟨3111683637701695567064003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074455758467797044709335 3111683637701695567064003)
                  ·
                    refine ⟨4667525456552543350596005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111683637701695567064003 4667525456552543350596005)
                    ·
                      refine ⟨875161023103601878236751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4667525456552543350596005 875161023103601878236751)
                      ·
                        rfl

theorem cell23_1704370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_1704370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704370 prefixEnd_1704370 := by exact prefixLift 1704370
  have htrace : WordTrace (prefixWord ++ tailWord_1704370) baseStart_1704370 baseEnd_1704370 := by
    simpa [prefixWord, tailWord_1704370, baseEnd_1704370] using wordTrace_append hprefix tailTrace_1704370
  have hstable : (prefixWord ++ tailWord_1704370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704370).length < 2 ^ (prefixWord ++ tailWord_1704370).sum := by decide
  have hdescent : baseEnd_1704370 < baseStart_1704370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704381 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_1704381 : Nat := 118140960795 + 1704381 * 2 ^ 59
def prefixEnd_1704381 : Nat := 4983230072969 + 3 ^ 40 * 1704381 * 2
def baseEnd_1704381 : Nat := 875166671390801335199201

theorem tailTrace_1704381 : CollatzResearch.WordTrace tailWord_1704381 prefixEnd_1704381 875166671390801335199201 := by
  unfold tailWord_1704381
  simp only [CollatzResearch.WordTrace]
  refine ⟨62163882038326196945440997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41442588025550797963627331 62163882038326196945440997)
  ·
    refine ⟨11655727882186161927270187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62163882038326196945440997 11655727882186161927270187)
    ·
      refine ⟨17483591823279242890905281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11655727882186161927270187 17483591823279242890905281)
      ·
        refine ⟨13112693867459432168178961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17483591823279242890905281 13112693867459432168178961)
        ·
          refine ⟨9834520400594574126134221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13112693867459432168178961 9834520400594574126134221)
          ·
            refine ⟨3687945150222965297300333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9834520400594574126134221 3687945150222965297300333)
            ·
              refine ⟨1382979431333611986487625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3687945150222965297300333 1382979431333611986487625)
              ·
                refine ⟨1037234573500208989865719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1382979431333611986487625 1037234573500208989865719)
                ·
                  refine ⟨1555851860250313484798579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037234573500208989865719 1555851860250313484798579)
                  ·
                    refine ⟨2333777790375470227197869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1555851860250313484798579 2333777790375470227197869)
                    ·
                      refine ⟨875166671390801335199201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333777790375470227197869 875166671390801335199201)
                      ·
                        rfl

theorem cell23_1704381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_1704381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704381 prefixEnd_1704381 := by exact prefixLift 1704381
  have htrace : WordTrace (prefixWord ++ tailWord_1704381) baseStart_1704381 baseEnd_1704381 := by
    simpa [prefixWord, tailWord_1704381, baseEnd_1704381] using wordTrace_append hprefix tailTrace_1704381
  have hstable : (prefixWord ++ tailWord_1704381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704381).length < 2 ^ (prefixWord ++ tailWord_1704381).sum := by decide
  have hdescent : baseEnd_1704381 < baseStart_1704381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704404 : List Nat := [2, 4, 1, 2, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1704404 : Nat := 118140960795 + 1704404 * 2 ^ 59
def prefixEnd_1704404 : Nat := 4983230072969 + 3 ^ 40 * 1704404 * 2
def baseEnd_1704404 : Nat := 875178481445854745211595

theorem tailTrace_1704404 : CollatzResearch.WordTrace tailWord_1704404 prefixEnd_1704404 875178481445854745211595 := by
  unfold tailWord_1704404
  simp only [CollatzResearch.WordTrace]
  refine ⟨31082360458621435936764133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41443147278161914582352177 31082360458621435936764133)
  ·
    refine ⟨5827942585991519238143275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31082360458621435936764133 5827942585991519238143275)
    ·
      refine ⟨8741913878987278857214913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5827942585991519238143275 8741913878987278857214913)
      ·
        refine ⟨6556435409240459142911185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8741913878987278857214913 6556435409240459142911185)
        ·
          refine ⟨4917326556930344357183389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6556435409240459142911185 4917326556930344357183389)
          ·
            refine ⟨1843997458848879133943771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4917326556930344357183389 1843997458848879133943771)
            ·
              refine ⟨2765996188273318700915657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1843997458848879133943771 2765996188273318700915657)
              ·
                refine ⟨2074497141204989025686743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2765996188273318700915657 2074497141204989025686743)
                ·
                  refine ⟨3111745711807483538530115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074497141204989025686743 3111745711807483538530115)
                  ·
                    refine ⟨4667618567711225307795173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3111745711807483538530115 4667618567711225307795173)
                    ·
                      refine ⟨875178481445854745211595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4667618567711225307795173 875178481445854745211595)
                      ·
                        rfl

theorem cell23_1704404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1704404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704404 prefixEnd_1704404 := by exact prefixLift 1704404
  have htrace : WordTrace (prefixWord ++ tailWord_1704404) baseStart_1704404 baseEnd_1704404 := by
    simpa [prefixWord, tailWord_1704404, baseEnd_1704404] using wordTrace_append hprefix tailTrace_1704404
  have hstable : (prefixWord ++ tailWord_1704404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704404).length < 2 ^ (prefixWord ++ tailWord_1704404).sum := by decide
  have hdescent : baseEnd_1704404 < baseStart_1704404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704424 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1704424 : Nat := 118140960795 + 1704424 * 2 ^ 59
def prefixEnd_1704424 : Nat := 4983230072969 + 3 ^ 40 * 1704424 * 2
def baseEnd_1704424 : Nat := 875188751058944666961503

theorem tailTrace_1704424 : CollatzResearch.WordTrace tailWord_1704424 prefixEnd_1704424 875188751058944666961503 := by
  unfold tailWord_1704424
  simp only [CollatzResearch.WordTrace]
  refine ⟨31082725188585207644628163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41443633584780276859504217 31082725188585207644628163)
  ·
    refine ⟨46624087782877811466942245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31082725188585207644628163 46624087782877811466942245)
    ·
      refine ⟨8742016459289589650051671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46624087782877811466942245 8742016459289589650051671)
      ·
        refine ⟨13113024688934384475077507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742016459289589650051671 13113024688934384475077507)
        ·
          refine ⟨19669537033401576712616261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13113024688934384475077507 19669537033401576712616261)
          ·
            refine ⟨3688038193762795633615549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19669537033401576712616261 3688038193762795633615549)
            ·
              refine ⟨1383014322661048362605831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3688038193762795633615549 1383014322661048362605831)
              ·
                refine ⟨2074521483991572543908747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383014322661048362605831 2074521483991572543908747)
                ·
                  refine ⟨3111782225987358815863121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074521483991572543908747 3111782225987358815863121)
                  ·
                    refine ⟨2333836669490519111897341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3111782225987358815863121 2333836669490519111897341)
                    ·
                      refine ⟨875188751058944666961503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2333836669490519111897341 875188751058944666961503)
                      ·
                        rfl

theorem cell23_1704424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1704424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704424 prefixEnd_1704424 := by exact prefixLift 1704424
  have htrace : WordTrace (prefixWord ++ tailWord_1704424) baseStart_1704424 baseEnd_1704424 := by
    simpa [prefixWord, tailWord_1704424, baseEnd_1704424] using wordTrace_append hprefix tailTrace_1704424
  have hstable : (prefixWord ++ tailWord_1704424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704424).length < 2 ^ (prefixWord ++ tailWord_1704424).sum := by decide
  have hdescent : baseEnd_1704424 < baseStart_1704424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704453 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_1704453 : Nat := 118140960795 + 1704453 * 2 ^ 59
def prefixEnd_1704453 : Nat := 4983230072969 + 3 ^ 40 * 1704453 * 2
def baseEnd_1704453 : Nat := 291734547332641684499623

theorem tailTrace_1704453 : CollatzResearch.WordTrace tailWord_1704453 prefixEnd_1704453 291734547332641684499623 := by
  unfold tailWord_1704453
  simp only [CollatzResearch.WordTrace]
  refine ⟨62166508094065353242062013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41444338729376902161374675 62166508094065353242062013)
  ·
    refine ⟨23312440535274507465773255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62166508094065353242062013 23312440535274507465773255)
    ·
      refine ⟨34968660802911761198659883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23312440535274507465773255 34968660802911761198659883)
      ·
        refine ⟨52452991204367641797989825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34968660802911761198659883 52452991204367641797989825)
        ·
          refine ⟨39339743403275731348492369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52452991204367641797989825 39339743403275731348492369)
          ·
            refine ⟨29504807552456798511369277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39339743403275731348492369 29504807552456798511369277)
            ·
              refine ⟨11064302832171299441763479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29504807552456798511369277 11064302832171299441763479)
              ·
                refine ⟨16596454248256949162645219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11064302832171299441763479 16596454248256949162645219)
                ·
                  refine ⟨24894681372385423743967829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16596454248256949162645219 24894681372385423743967829)
                  ·
                    refine ⟨291734547332641684499623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24894681372385423743967829 291734547332641684499623)
                    ·
                      rfl

theorem cell23_1704453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_1704453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704453 prefixEnd_1704453 := by exact prefixLift 1704453
  have htrace : WordTrace (prefixWord ++ tailWord_1704453) baseStart_1704453 baseEnd_1704453 := by
    simpa [prefixWord, tailWord_1704453, baseEnd_1704453] using wordTrace_append hprefix tailTrace_1704453
  have hstable : (prefixWord ++ tailWord_1704453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704453).length < 2 ^ (prefixWord ++ tailWord_1704453).sum := by decide
  have hdescent : baseEnd_1704453 < baseStart_1704453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704511 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 2, 2, 2]
def baseStart_1704511 : Nat := 118140960795 + 1704511 * 2 ^ 59
def prefixEnd_1704511 : Nat := 4983230072969 + 3 ^ 40 * 1704511 * 2
def baseEnd_1704511 : Nat := 875233423875885826573603

theorem tailTrace_1704511 : CollatzResearch.WordTrace tailWord_1704511 prefixEnd_1704511 875233423875885826573603 := by
  unfold tailWord_1704511
  simp only [CollatzResearch.WordTrace]
  refine ⟨62168623527855229147673387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41445749018570152765115591 62168623527855229147673387)
  ·
    refine ⟨93252935291782843721510081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62168623527855229147673387 93252935291782843721510081)
    ·
      refine ⟨69939701468837132791132561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93252935291782843721510081 69939701468837132791132561)
      ·
        refine ⟨52454776101627849593349421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69939701468837132791132561 52454776101627849593349421)
        ·
          refine ⟨19670541038110443597506033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52454776101627849593349421 19670541038110443597506033)
          ·
            refine ⟨14752905778582832698129525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19670541038110443597506033 14752905778582832698129525)
            ·
              refine ⟨1383084916742140565449643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14752905778582832698129525 1383084916742140565449643)
              ·
                refine ⟨2074627375113210848174465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383084916742140565449643 2074627375113210848174465)
                ·
                  refine ⟨1555970531334908136130849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2074627375113210848174465 1555970531334908136130849)
                  ·
                    refine ⟨1166977898501181102098137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1555970531334908136130849 1166977898501181102098137)
                    ·
                      refine ⟨875233423875885826573603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1166977898501181102098137 875233423875885826573603)
                      ·
                        rfl

theorem cell23_1704511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_1704511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704511 prefixEnd_1704511 := by exact prefixLift 1704511
  have htrace : WordTrace (prefixWord ++ tailWord_1704511) baseStart_1704511 baseEnd_1704511 := by
    simpa [prefixWord, tailWord_1704511, baseEnd_1704511] using wordTrace_append hprefix tailTrace_1704511
  have hstable : (prefixWord ++ tailWord_1704511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704511).length < 2 ^ (prefixWord ++ tailWord_1704511).sum := by decide
  have hdescent : baseEnd_1704511 < baseStart_1704511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704530 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1704530 : Nat := 118140960795 + 1704530 * 2 ^ 59
def prefixEnd_1704530 : Nat := 4983230072969 + 3 ^ 40 * 1704530 * 2
def baseEnd_1704530 : Nat := 291747726669440417412005

theorem tailTrace_1704530 : CollatzResearch.WordTrace tailWord_1704530 prefixEnd_1704530 291747726669440417412005 := by
  unfold tailWord_1704530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15542329128696598848153761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41446211009857596928410029 15542329128696598848153761)
  ·
    refine ⟨11656746846522449136115321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15542329128696598848153761 11656746846522449136115321)
    ·
      refine ⟨8742560134891836852086491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11656746846522449136115321 8742560134891836852086491)
      ·
        refine ⟨13113840202337755278129737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742560134891836852086491 13113840202337755278129737)
        ·
          refine ⟨9835380151753316458597303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13113840202337755278129737 9835380151753316458597303)
          ·
            refine ⟨14753070227629974687895955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9835380151753316458597303 14753070227629974687895955)
            ·
              refine ⟨22129605341444962031843933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14753070227629974687895955 22129605341444962031843933)
              ·
                refine ⟨8298602003041860761941475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22129605341444962031843933 8298602003041860761941475)
                ·
                  refine ⟨12447903004562791142912213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8298602003041860761941475 12447903004562791142912213)
                  ·
                    refine ⟨291747726669440417412005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12447903004562791142912213 291747726669440417412005)
                    ·
                      rfl

theorem cell23_1704530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1704530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704530 prefixEnd_1704530 := by exact prefixLift 1704530
  have htrace : WordTrace (prefixWord ++ tailWord_1704530) baseStart_1704530 baseEnd_1704530 := by
    simpa [prefixWord, tailWord_1704530, baseEnd_1704530] using wordTrace_append hprefix tailTrace_1704530
  have hstable : (prefixWord ++ tailWord_1704530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704530).length < 2 ^ (prefixWord ++ tailWord_1704530).sum := by decide
  have hdescent : baseEnd_1704530 < baseStart_1704530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704557 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1704557 : Nat := 118140960795 + 1704557 * 2 ^ 59
def prefixEnd_1704557 : Nat := 4983230072969 + 3 ^ 40 * 1704557 * 2
def baseEnd_1704557 : Nat := 875257043985992646598391

theorem tailTrace_1704557 : CollatzResearch.WordTrace tailWord_1704557 prefixEnd_1704557 875257043985992646598391 := by
  unfold tailWord_1704557
  simp only [CollatzResearch.WordTrace]
  refine ⟨62170301285688579003847925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41446867523792386002565283 62170301285688579003847925)
  ·
    refine ⟨5828465745533304281610743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62170301285688579003847925 5828465745533304281610743)
    ·
      refine ⟨8742698618299956422416115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828465745533304281610743 8742698618299956422416115)
      ·
        refine ⟨13114047927449934633624173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742698618299956422416115 13114047927449934633624173)
        ·
          refine ⟨4917767972793725487609065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13114047927449934633624173 4917767972793725487609065)
          ·
            refine ⟨3688325979595294115706799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4917767972793725487609065 3688325979595294115706799)
            ·
              refine ⟨5532488969392941173560199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688325979595294115706799 5532488969392941173560199)
              ·
                refine ⟨8298733454089411760340299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532488969392941173560199 8298733454089411760340299)
                ·
                  refine ⟨12448100181134117640510449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8298733454089411760340299 12448100181134117640510449)
                  ·
                    refine ⟨9336075135850588230382837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12448100181134117640510449 9336075135850588230382837)
                    ·
                      refine ⟨875257043985992646598391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9336075135850588230382837 875257043985992646598391)
                      ·
                        rfl

theorem cell23_1704557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1704557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704557 prefixEnd_1704557 := by exact prefixLift 1704557
  have htrace : WordTrace (prefixWord ++ tailWord_1704557) baseStart_1704557 baseEnd_1704557 := by
    simpa [prefixWord, tailWord_1704557, baseEnd_1704557] using wordTrace_append hprefix tailTrace_1704557
  have hstable : (prefixWord ++ tailWord_1704557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704557).length < 2 ^ (prefixWord ++ tailWord_1704557).sum := by decide
  have hdescent : baseEnd_1704557 < baseStart_1704557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704567 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 2, 4, 2]
def baseStart_1704567 : Nat := 118140960795 + 1704567 * 2 ^ 59
def prefixEnd_1704567 : Nat := 4983230072969 + 3 ^ 40 * 1704567 * 2
def baseEnd_1704567 : Nat := 875262178792537607473345

theorem tailTrace_1704567 : CollatzResearch.WordTrace tailWord_1704567 prefixEnd_1704567 875262178792537607473345 := by
  unfold tailWord_1704567
  simp only [CollatzResearch.WordTrace]
  refine ⟨62170666015652350711711955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41447110677101567141141303 62170666015652350711711955)
  ·
    refine ⟨93255999023478526067567933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62170666015652350711711955 93255999023478526067567933)
    ·
      refine ⟨34970999633804447275337975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93255999023478526067567933 34970999633804447275337975)
      ·
        refine ⟨52456499450706670913006963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34970999633804447275337975 52456499450706670913006963)
        ·
          refine ⟨78684749176060006369510445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52456499450706670913006963 78684749176060006369510445)
          ·
            refine ⟨29506780941022502388566417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78684749176060006369510445 29506780941022502388566417)
            ·
              refine ⟨22130085705766876791424813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29506780941022502388566417 22130085705766876791424813)
              ·
                refine ⟨8298782139662578796784305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22130085705766876791424813 8298782139662578796784305)
                ·
                  refine ⟨6224086604746934097588229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8298782139662578796784305 6224086604746934097588229)
                  ·
                    refine ⟨1167016238390050143297793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224086604746934097588229 1167016238390050143297793)
                    ·
                      refine ⟨875262178792537607473345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167016238390050143297793 875262178792537607473345)
                      ·
                        rfl

theorem cell23_1704567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 4, 2].length) (baseStart_1704567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704567 prefixEnd_1704567 := by exact prefixLift 1704567
  have htrace : WordTrace (prefixWord ++ tailWord_1704567) baseStart_1704567 baseEnd_1704567 := by
    simpa [prefixWord, tailWord_1704567, baseEnd_1704567] using wordTrace_append hprefix tailTrace_1704567
  have hstable : (prefixWord ++ tailWord_1704567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704567).length < 2 ^ (prefixWord ++ tailWord_1704567).sum := by decide
  have hdescent : baseEnd_1704567 < baseStart_1704567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704577 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1704577 : Nat := 118140960795 + 1704577 * 2 ^ 59
def prefixEnd_1704577 : Nat := 4983230072969 + 3 ^ 40 * 1704577 * 2
def baseEnd_1704577 : Nat := 291755771199694189449433

theorem tailTrace_1704577 : CollatzResearch.WordTrace tailWord_1704577 prefixEnd_1704577 291755771199694189449433 := by
  unfold tailWord_1704577
  simp only [CollatzResearch.WordTrace]
  refine ⟨62171030745616122419575985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41447353830410748279717323 62171030745616122419575985)
  ·
    refine ⟨46628273059212091814681989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62171030745616122419575985 46628273059212091814681989)
    ·
      refine ⟨8742801198602267215252873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46628273059212091814681989 8742801198602267215252873)
      ·
        refine ⟨6557100898951700411439655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8742801198602267215252873 6557100898951700411439655)
        ·
          refine ⟨9835651348427550617159483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557100898951700411439655 9835651348427550617159483)
          ·
            refine ⟨14753477022641325925739225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9835651348427550617159483 14753477022641325925739225)
            ·
              refine ⟨11065107766980994444304419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14753477022641325925739225 11065107766980994444304419)
              ·
                refine ⟨16597661650471491666456629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11065107766980994444304419 16597661650471491666456629)
                ·
                  refine ⟨1556030779731702343730309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16597661650471491666456629 1556030779731702343730309)
                  ·
                    refine ⟨291755771199694189449433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556030779731702343730309 291755771199694189449433)
                    ·
                      rfl

theorem cell23_1704577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1704577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704577 prefixEnd_1704577 := by exact prefixLift 1704577
  have htrace : WordTrace (prefixWord ++ tailWord_1704577) baseStart_1704577 baseEnd_1704577 := by
    simpa [prefixWord, tailWord_1704577, baseEnd_1704577] using wordTrace_append hprefix tailTrace_1704577
  have hstable : (prefixWord ++ tailWord_1704577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704577).length < 2 ^ (prefixWord ++ tailWord_1704577).sum := by decide
  have hdescent : baseEnd_1704577 < baseStart_1704577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704604 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_1704604 : Nat := 118140960795 + 1704604 * 2 ^ 59
def prefixEnd_1704604 : Nat := 4983230072969 + 3 ^ 40 * 1704604 * 2
def baseEnd_1704604 : Nat := 875281177576753962710675

theorem tailTrace_1704604 : CollatzResearch.WordTrace tailWord_1704604 prefixEnd_1704604 875281177576753962710675 := by
  unfold tailWord_1704604
  simp only [CollatzResearch.WordTrace]
  refine ⟨31086007758259153015404433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41448010344345537353872577 31086007758259153015404433)
  ·
    refine ⟨23314505818694364761553325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31086007758259153015404433 23314505818694364761553325)
    ·
      refine ⟨8742939682010386785582497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23314505818694364761553325 8742939682010386785582497)
      ·
        refine ⟨6557204761507790089186873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8742939682010386785582497 6557204761507790089186873)
        ·
          refine ⟨4917903571130842566890155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6557204761507790089186873 4917903571130842566890155)
          ·
            refine ⟨7376855356696263850335233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4917903571130842566890155 7376855356696263850335233)
            ·
              refine ⟨5532641517522197887751425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7376855356696263850335233 5532641517522197887751425)
              ·
                refine ⟨4149481138141648415813569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532641517522197887751425 4149481138141648415813569)
                ·
                  refine ⟨3112110853606236311860177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149481138141648415813569 3112110853606236311860177)
                  ·
                    refine ⟨2334083140204677233895133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112110853606236311860177 2334083140204677233895133)
                    ·
                      refine ⟨875281177576753962710675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334083140204677233895133 875281177576753962710675)
                      ·
                        rfl

theorem cell23_1704604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_1704604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704604 prefixEnd_1704604 := by exact prefixLift 1704604
  have htrace : WordTrace (prefixWord ++ tailWord_1704604) baseStart_1704604 baseEnd_1704604 := by
    simpa [prefixWord, tailWord_1704604, baseEnd_1704604] using wordTrace_append hprefix tailTrace_1704604
  have hstable : (prefixWord ++ tailWord_1704604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704604).length < 2 ^ (prefixWord ++ tailWord_1704604).sum := by decide
  have hdescent : baseEnd_1704604 < baseStart_1704604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704618 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1704618 : Nat := 118140960795 + 1704618 * 2 ^ 59
def prefixEnd_1704618 : Nat := 4983230072969 + 3 ^ 40 * 1704618 * 2
def baseEnd_1704618 : Nat := 875288366305916907935611

theorem tailTrace_1704618 : CollatzResearch.WordTrace tailWord_1704618 prefixEnd_1704618 875288366305916907935611 := by
  unfold tailWord_1704618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15543131534616896605454627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41448350758978390947879005 15543131534616896605454627)
  ·
    refine ⟨23314697301925344908181941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15543131534616896605454627 23314697301925344908181941)
    ·
      refine ⟨2185752872055501085142057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23314697301925344908181941 2185752872055501085142057)
      ·
        refine ⟨1639314654041625813856543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2185752872055501085142057 1639314654041625813856543)
        ·
          refine ⟨2458971981062438720784815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639314654041625813856543 2458971981062438720784815)
          ·
            refine ⟨3688457971593658081177223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458971981062438720784815 3688457971593658081177223)
            ·
              refine ⟨5532686957390487121765835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688457971593658081177223 5532686957390487121765835)
              ·
                refine ⟨8299030436085730682648753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532686957390487121765835 8299030436085730682648753)
                ·
                  refine ⟨6224272827064298011986565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8299030436085730682648753 6224272827064298011986565)
                  ·
                    refine ⟨1167051155074555877247481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224272827064298011986565 1167051155074555877247481)
                    ·
                      refine ⟨875288366305916907935611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167051155074555877247481 875288366305916907935611)
                      ·
                        rfl

theorem cell23_1704618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1704618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704618 prefixEnd_1704618 := by exact prefixLift 1704618
  have htrace : WordTrace (prefixWord ++ tailWord_1704618) baseStart_1704618 baseEnd_1704618 := by
    simpa [prefixWord, tailWord_1704618, baseEnd_1704618] using wordTrace_append hprefix tailTrace_1704618
  have hstable : (prefixWord ++ tailWord_1704618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704618).length < 2 ^ (prefixWord ++ tailWord_1704618).sum := by decide
  have hdescent : baseEnd_1704618 < baseStart_1704618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704634 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_1704634 : Nat := 118140960795 + 1704634 * 2 ^ 59
def prefixEnd_1704634 : Nat := 4983230072969 + 3 ^ 40 * 1704634 * 2
def baseEnd_1704634 : Nat := 875296581996388845335537

theorem tailTrace_1704634 : CollatzResearch.WordTrace tailWord_1704634 prefixEnd_1704634 875296581996388845335537 := by
  unfold tailWord_1704634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15543277426602405288600239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41448739804273080769600637 15543277426602405288600239)
  ·
    refine ⟨23314916139903607932900359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15543277426602405288600239 23314916139903607932900359)
    ·
      refine ⟨34972374209855411899350539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23314916139903607932900359 34972374209855411899350539)
      ·
        refine ⟨52458561314783117849025809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34972374209855411899350539 52458561314783117849025809)
        ·
          refine ⟨39343920986087338386769357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52458561314783117849025809 39343920986087338386769357)
          ·
            refine ⟨14753970369782751895038509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39343920986087338386769357 14753970369782751895038509)
            ·
              refine ⟨5532738888668531960639441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14753970369782751895038509 5532738888668531960639441)
              ·
                refine ⟨4149554166501398970479581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532738888668531960639441 4149554166501398970479581)
                ·
                  refine ⟨1556082812438024613929843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4149554166501398970479581 1556082812438024613929843)
                  ·
                    refine ⟨2334124218657036920894765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556082812438024613929843 2334124218657036920894765)
                    ·
                      refine ⟨875296581996388845335537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334124218657036920894765 875296581996388845335537)
                      ·
                        rfl

theorem cell23_1704634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_1704634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704634 prefixEnd_1704634 := by exact prefixLift 1704634
  have htrace : WordTrace (prefixWord ++ tailWord_1704634) baseStart_1704634 baseEnd_1704634 := by
    simpa [prefixWord, tailWord_1704634, baseEnd_1704634] using wordTrace_append hprefix tailTrace_1704634
  have hstable : (prefixWord ++ tailWord_1704634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704634).length < 2 ^ (prefixWord ++ tailWord_1704634).sum := by decide
  have hdescent : baseEnd_1704634 < baseStart_1704634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704637 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1704637 : Nat := 118140960795 + 1704637 * 2 ^ 59
def prefixEnd_1704637 : Nat := 4983230072969 + 3 ^ 40 * 1704637 * 2
def baseEnd_1704637 : Nat := 291766040812784111199341

theorem tailTrace_1704637 : CollatzResearch.WordTrace tailWord_1704637 prefixEnd_1704637 291766040812784111199341 := by
  unfold tailWord_1704637
  simp only [CollatzResearch.WordTrace]
  refine ⟨62173219125398752666760165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41448812750265835111173443 62173219125398752666760165)
  ·
    refine ⟨11657478586012266125017531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62173219125398752666760165 11657478586012266125017531)
    ·
      refine ⟨17486217879018399187526297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11657478586012266125017531 17486217879018399187526297)
      ·
        refine ⟨13114663409263799390644723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17486217879018399187526297 13114663409263799390644723)
        ·
          refine ⟨19671995113895699085967085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13114663409263799390644723 19671995113895699085967085)
          ·
            refine ⟨7376998167710887157237657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19671995113895699085967085 7376998167710887157237657)
            ·
              refine ⟨5532748625783165367928243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7376998167710887157237657 5532748625783165367928243)
              ·
                refine ⟨8299122938674748051892365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532748625783165367928243 8299122938674748051892365)
                ·
                  refine ⟨3112171102003030519459637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8299122938674748051892365 3112171102003030519459637)
                  ·
                    refine ⟨291766040812784111199341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3112171102003030519459637 291766040812784111199341)
                    ·
                      rfl

theorem cell23_1704637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1704637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704637 prefixEnd_1704637 := by exact prefixLift 1704637
  have htrace : WordTrace (prefixWord ++ tailWord_1704637) baseStart_1704637 baseEnd_1704637 := by
    simpa [prefixWord, tailWord_1704637, baseEnd_1704637] using wordTrace_append hprefix tailTrace_1704637
  have hstable : (prefixWord ++ tailWord_1704637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704637).length < 2 ^ (prefixWord ++ tailWord_1704637).sum := by decide
  have hdescent : baseEnd_1704637 < baseStart_1704637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704654 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_1704654 : Nat := 118140960795 + 1704654 * 2 ^ 59
def prefixEnd_1704654 : Nat := 4983230072969 + 3 ^ 40 * 1704654 * 2
def baseEnd_1704654 : Nat := 291768950536492922361815

theorem tailTrace_1704654 : CollatzResearch.WordTrace tailWord_1704654 prefixEnd_1704654 291768950536492922361815 := by
  unfold tailWord_1704654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7771729895792145571266127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41449226110891443046752677 7771729895792145571266127)
  ·
    refine ⟨11657594843688218356899191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7771729895792145571266127 11657594843688218356899191)
    ·
      refine ⟨17486392265532327535348787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11657594843688218356899191 17486392265532327535348787)
      ·
        refine ⟨26229588398298491303023181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17486392265532327535348787 26229588398298491303023181)
        ·
          refine ⟨9836095649361934238633693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26229588398298491303023181 9836095649361934238633693)
          ·
            refine ⟨3688535868510725339487635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9836095649361934238633693 3688535868510725339487635)
            ·
              refine ⟨5532803802766088009231453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688535868510725339487635 5532803802766088009231453)
              ·
                refine ⟨2074801426037283003461795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5532803802766088009231453 2074801426037283003461795)
                ·
                  refine ⟨3112202139055924505192693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074801426037283003461795 3112202139055924505192693)
                  ·
                    refine ⟨291768950536492922361815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3112202139055924505192693 291768950536492922361815)
                    ·
                      rfl

theorem cell23_1704654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_1704654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704654 prefixEnd_1704654 := by exact prefixLift 1704654
  have htrace : WordTrace (prefixWord ++ tailWord_1704654) baseStart_1704654 baseEnd_1704654 := by
    simpa [prefixWord, tailWord_1704654, baseEnd_1704654] using wordTrace_append hprefix tailTrace_1704654
  have hstable : (prefixWord ++ tailWord_1704654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704654).length < 2 ^ (prefixWord ++ tailWord_1704654).sum := by decide
  have hdescent : baseEnd_1704654 < baseStart_1704654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704668 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1704668 : Nat := 118140960795 + 1704668 * 2 ^ 59
def prefixEnd_1704668 : Nat := 4983230072969 + 3 ^ 40 * 1704668 * 2
def baseEnd_1704668 : Nat := 875314040338641712310381

theorem tailTrace_1704668 : CollatzResearch.WordTrace tailWord_1704668 prefixEnd_1704668 875314040338641712310381 := by
  unfold tailWord_1704668
  simp only [CollatzResearch.WordTrace]
  refine ⟨31087174894143222480569329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41449566525524296640759105 31087174894143222480569329)
  ·
    refine ⟨23315381170607416860426997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31087174894143222480569329 23315381170607416860426997)
    ·
      refine ⟨2185816984744445330665031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23315381170607416860426997 2185816984744445330665031)
      ·
        refine ⟨3278725477116667995997547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185816984744445330665031 3278725477116667995997547)
        ·
          refine ⟨4918088215675001993996321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3278725477116667995997547 4918088215675001993996321)
          ·
            refine ⟨3688566161756251495497241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4918088215675001993996321 3688566161756251495497241)
            ·
              refine ⟨2766424621317188621622931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3688566161756251495497241 2766424621317188621622931)
              ·
                refine ⟨4149636931975782932434397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766424621317188621622931 4149636931975782932434397)
                ·
                  refine ⟨1556113849490918599662899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4149636931975782932434397 1556113849490918599662899)
                  ·
                    refine ⟨2334170774236377899494349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556113849490918599662899 2334170774236377899494349)
                    ·
                      refine ⟨875314040338641712310381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334170774236377899494349 875314040338641712310381)
                      ·
                        rfl

theorem cell23_1704668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1704668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704668 prefixEnd_1704668 := by exact prefixLift 1704668
  have htrace : WordTrace (prefixWord ++ tailWord_1704668) baseStart_1704668 baseEnd_1704668 := by
    simpa [prefixWord, tailWord_1704668, baseEnd_1704668] using wordTrace_append hprefix tailTrace_1704668
  have hstable : (prefixWord ++ tailWord_1704668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704668).length < 2 ^ (prefixWord ++ tailWord_1704668).sum := by decide
  have hdescent : baseEnd_1704668 < baseStart_1704668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704677 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1704677 : Nat := 118140960795 + 1704677 * 2 ^ 59
def prefixEnd_1704677 : Nat := 4983230072969 + 3 ^ 40 * 1704677 * 2
def baseEnd_1704677 : Nat := 875318661664532177097839

theorem tailTrace_1704677 : CollatzResearch.WordTrace tailWord_1704677 prefixEnd_1704677 875318661664532177097839 := by
  unfold tailWord_1704677
  simp only [CollatzResearch.WordTrace]
  refine ⟨62174678045253839498216285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41449785363502559665477523 62174678045253839498216285)
  ·
    refine ⟨23315504266970189811831107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62174678045253839498216285 23315504266970189811831107)
    ·
      refine ⟨34973256400455284717746661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23315504266970189811831107 34973256400455284717746661)
      ·
        refine ⟨6557485575085365884577499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34973256400455284717746661 6557485575085365884577499)
        ·
          refine ⟨9836228362628048826866249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557485575085365884577499 9836228362628048826866249)
          ·
            refine ⟨7377171271971036620149687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9836228362628048826866249 7377171271971036620149687)
            ·
              refine ⟨11065756907956554930224531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377171271971036620149687 11065756907956554930224531)
              ·
                refine ⟨16598635361934832395336797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11065756907956554930224531 16598635361934832395336797)
                ·
                  refine ⟨6224488260725562148251299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16598635361934832395336797 6224488260725562148251299)
                  ·
                    refine ⟨9336732391088343222376949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6224488260725562148251299 9336732391088343222376949)
                    ·
                      refine ⟨875318661664532177097839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9336732391088343222376949 875318661664532177097839)
                      ·
                        rfl

theorem cell23_1704677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1704677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704677 prefixEnd_1704677 := by exact prefixLift 1704677
  have htrace : WordTrace (prefixWord ++ tailWord_1704677) baseStart_1704677 baseEnd_1704677 := by
    simpa [prefixWord, tailWord_1704677, baseEnd_1704677] using wordTrace_append hprefix tailTrace_1704677
  have hstable : (prefixWord ++ tailWord_1704677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704677).length < 2 ^ (prefixWord ++ tailWord_1704677).sum := by decide
  have hdescent : baseEnd_1704677 < baseStart_1704677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704687 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_1704687 : Nat := 118140960795 + 1704687 * 2 ^ 59
def prefixEnd_1704687 : Nat := 4983230072969 + 3 ^ 40 * 1704687 * 2
def baseEnd_1704687 : Nat := 875323796471077137972793

theorem tailTrace_1704687 : CollatzResearch.WordTrace tailWord_1704687 prefixEnd_1704687 875323796471077137972793 := by
  unfold tailWord_1704687
  simp only [CollatzResearch.WordTrace]
  refine ⟨62175042775217611206080315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41450028516811740804053543 62175042775217611206080315)
  ·
    refine ⟨93262564162826416809120473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62175042775217611206080315 93262564162826416809120473)
    ·
      refine ⟨69946923122119812606840355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93262564162826416809120473 69946923122119812606840355)
      ·
        refine ⟨104920384683179718910260533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69946923122119812606840355 104920384683179718910260533)
        ·
          refine ⟨9836286064048098647836925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104920384683179718910260533 9836286064048098647836925)
          ·
            refine ⟨3688607274018036992938847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9836286064048098647836925 3688607274018036992938847)
            ·
              refine ⟨5532910911027055489408271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688607274018036992938847 5532910911027055489408271)
              ·
                refine ⟨8299366366540583234112407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532910911027055489408271 8299366366540583234112407)
                ·
                  refine ⟨12449049549810874851168611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299366366540583234112407 12449049549810874851168611)
                  ·
                    refine ⟨18673574324716312276752917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12449049549810874851168611 18673574324716312276752917)
                    ·
                      refine ⟨875323796471077137972793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18673574324716312276752917 875323796471077137972793)
                      ·
                        rfl

theorem cell23_1704687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_1704687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704687 prefixEnd_1704687 := by exact prefixLift 1704687
  have htrace : WordTrace (prefixWord ++ tailWord_1704687) baseStart_1704687 baseEnd_1704687 := by
    simpa [prefixWord, tailWord_1704687, baseEnd_1704687] using wordTrace_append hprefix tailTrace_1704687
  have hstable : (prefixWord ++ tailWord_1704687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704687).length < 2 ^ (prefixWord ++ tailWord_1704687).sum := by decide
  have hdescent : baseEnd_1704687 < baseStart_1704687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704707 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1704707 : Nat := 118140960795 + 1704707 * 2 ^ 59
def prefixEnd_1704707 : Nat := 4983230072969 + 3 ^ 40 * 1704707 * 2
def baseEnd_1704707 : Nat := 875334066084167059722701

theorem tailTrace_1704707 : CollatzResearch.WordTrace tailWord_1704707 prefixEnd_1704707 875334066084167059722701 := by
  unfold tailWord_1704707
  simp only [CollatzResearch.WordTrace]
  refine ⟨62175772235145154621808375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41450514823430103081205583 62175772235145154621808375)
  ·
    refine ⟨93263658352717731932712563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62175772235145154621808375 93263658352717731932712563)
    ·
      refine ⟨139895487529076597899068845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93263658352717731932712563 139895487529076597899068845)
      ·
        refine ⟨52460807823403724212150817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139895487529076597899068845 52460807823403724212150817)
        ·
          refine ⟨39345605867552793159113113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52460807823403724212150817 39345605867552793159113113)
          ·
            refine ⟨29509204400664594869334835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39345605867552793159113113 29509204400664594869334835)
            ·
              refine ⟨44263806600996892304002253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29509204400664594869334835 44263806600996892304002253)
              ·
                refine ⟨16598927475373834614000845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44263806600996892304002253 16598927475373834614000845)
                ·
                  refine ⟨6224597803265187980250317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16598927475373834614000845 6224597803265187980250317)
                  ·
                    refine ⟨2334224176224445492593869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6224597803265187980250317 2334224176224445492593869)
                    ·
                      refine ⟨875334066084167059722701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334224176224445492593869 875334066084167059722701)
                      ·
                        rfl

theorem cell23_1704707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1704707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704707 prefixEnd_1704707 := by exact prefixLift 1704707
  have htrace : WordTrace (prefixWord ++ tailWord_1704707) baseStart_1704707 baseEnd_1704707 := by
    simpa [prefixWord, tailWord_1704707, baseEnd_1704707] using wordTrace_append hprefix tailTrace_1704707
  have hstable : (prefixWord ++ tailWord_1704707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704707).length < 2 ^ (prefixWord ++ tailWord_1704707).sum := by decide
  have hdescent : baseEnd_1704707 < baseStart_1704707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704711 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1704711 : Nat := 118140960795 + 1704711 * 2 ^ 59
def prefixEnd_1704711 : Nat := 4983230072969 + 3 ^ 40 * 1704711 * 2
def baseEnd_1704711 : Nat := 875336120006785044072683

theorem tailTrace_1704711 : CollatzResearch.WordTrace tailWord_1704711 prefixEnd_1704711 875336120006785044072683 := by
  unfold tailWord_1704711
  simp only [CollatzResearch.WordTrace]
  refine ⟨62175918127130663304953987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41450612084753775536635991 62175918127130663304953987)
  ·
    refine ⟨93263877190695994957430981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62175918127130663304953987 93263877190695994957430981)
    ·
      refine ⟨17486976973255499054518309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93263877190695994957430981 17486976973255499054518309)
      ·
        refine ⟨3278808182485406072722183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17486976973255499054518309 3278808182485406072722183)
        ·
          refine ⟨4918212273728109109083275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3278808182485406072722183 4918212273728109109083275)
          ·
            refine ⟨7377318410592163663624913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918212273728109109083275 7377318410592163663624913)
            ·
              refine ⟨5532988807944122747718685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377318410592163663624913 5532988807944122747718685)
              ·
                refine ⟨2074870802979046030394507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5532988807944122747718685 2074870802979046030394507)
                ·
                  refine ⟨3112306204468569045591761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074870802979046030394507 3112306204468569045591761)
                  ·
                    refine ⟨2334229653351426784193821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3112306204468569045591761 2334229653351426784193821)
                    ·
                      refine ⟨875336120006785044072683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334229653351426784193821 875336120006785044072683)
                      ·
                        rfl

theorem cell23_1704711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1704711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704711 prefixEnd_1704711 := by exact prefixLift 1704711
  have htrace : WordTrace (prefixWord ++ tailWord_1704711) baseStart_1704711 baseEnd_1704711 := by
    simpa [prefixWord, tailWord_1704711, baseEnd_1704711] using wordTrace_append hprefix tailTrace_1704711
  have hstable : (prefixWord ++ tailWord_1704711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704711).length < 2 ^ (prefixWord ++ tailWord_1704711).sum := by decide
  have hdescent : baseEnd_1704711 < baseStart_1704711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704725 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_1704725 : Nat := 118140960795 + 1704725 * 2 ^ 59
def prefixEnd_1704725 : Nat := 4983230072969 + 3 ^ 40 * 1704725 * 2
def baseEnd_1704725 : Nat := 875343308735947989297619

theorem tailTrace_1704725 : CollatzResearch.WordTrace tailWord_1704725 prefixEnd_1704725 875343308735947989297619 := by
  unfold tailWord_1704725
  simp only [CollatzResearch.WordTrace]
  refine ⟨62176428749079943695963629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41450952499386629130642419 62176428749079943695963629)
  ·
    refine ⟨23316160780904978885986361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62176428749079943695963629 23316160780904978885986361)
    ·
      refine ⟨17487120585678734164489771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23316160780904978885986361 17487120585678734164489771)
      ·
        refine ⟨26230680878518101246734657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17487120585678734164489771 26230680878518101246734657)
        ·
          refine ⟨19673010658888575935050993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26230680878518101246734657 19673010658888575935050993)
          ·
            refine ⟨14754757994166431951288245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19673010658888575935050993 14754757994166431951288245)
            ·
              refine ⟨1383258561953102995433273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14754757994166431951288245 1383258561953102995433273)
              ·
                refine ⟨1037443921464827246574955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383258561953102995433273 1037443921464827246574955)
                ·
                  refine ⟨1556165882197240869862433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037443921464827246574955 1556165882197240869862433)
                  ·
                    refine ⟨1167124411647930652396825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1556165882197240869862433 1167124411647930652396825)
                    ·
                      refine ⟨875343308735947989297619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167124411647930652396825 875343308735947989297619)
                      ·
                        rfl

theorem cell23_1704725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_1704725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704725 prefixEnd_1704725 := by exact prefixLift 1704725
  have htrace : WordTrace (prefixWord ++ tailWord_1704725) baseStart_1704725 baseEnd_1704725 := by
    simpa [prefixWord, tailWord_1704725, baseEnd_1704725] using wordTrace_append hprefix tailTrace_1704725
  have hstable : (prefixWord ++ tailWord_1704725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704725).length < 2 ^ (prefixWord ++ tailWord_1704725).sum := by decide
  have hdescent : baseEnd_1704725 < baseStart_1704725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704741 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_1704741 : Nat := 118140960795 + 1704741 * 2 ^ 59
def prefixEnd_1704741 : Nat := 4983230072969 + 3 ^ 40 * 1704741 * 2
def baseEnd_1704741 : Nat := 875351524426419926697545

theorem tailTrace_1704741 : CollatzResearch.WordTrace tailWord_1704741 prefixEnd_1704741 875351524426419926697545 := by
  unfold tailWord_1704741
  simp only [CollatzResearch.WordTrace]
  refine ⟨62177012317021978428546077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41451341544681318952364051 62177012317021978428546077)
  ·
    refine ⟨23316379618883241910704779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62177012317021978428546077 23316379618883241910704779)
    ·
      refine ⟨34974569428324862866057169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23316379618883241910704779 34974569428324862866057169)
      ·
        refine ⟨26230927071243647149542877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34974569428324862866057169 26230927071243647149542877)
        ·
          refine ⟨9836597651716367681078579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26230927071243647149542877 9836597651716367681078579)
          ·
            refine ⟨14754896477574551521617869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9836597651716367681078579 14754896477574551521617869)
            ·
              refine ⟨5533086179090456820606701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14754896477574551521617869 5533086179090456820606701)
              ·
                refine ⟨2074907317158921307727513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5533086179090456820606701 2074907317158921307727513)
                ·
                  refine ⟨1556180487869190980795635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2074907317158921307727513 1556180487869190980795635)
                  ·
                    refine ⟨2334270731803786471193453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556180487869190980795635 2334270731803786471193453)
                    ·
                      refine ⟨875351524426419926697545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334270731803786471193453 875351524426419926697545)
                      ·
                        rfl

theorem cell23_1704741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_1704741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704741 prefixEnd_1704741 := by exact prefixLift 1704741
  have htrace : WordTrace (prefixWord ++ tailWord_1704741) baseStart_1704741 baseEnd_1704741 := by
    simpa [prefixWord, tailWord_1704741, baseEnd_1704741] using wordTrace_append hprefix tailTrace_1704741
  have hstable : (prefixWord ++ tailWord_1704741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704741).length < 2 ^ (prefixWord ++ tailWord_1704741).sum := by decide
  have hdescent : baseEnd_1704741 < baseStart_1704741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704758 : List Nat := [5, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1704758 : Nat := 118140960795 + 1704758 * 2 ^ 59
def prefixEnd_1704758 : Nat := 4983230072969 + 3 ^ 40 * 1704758 * 2
def baseEnd_1704758 : Nat := 875360253597546360184967

theorem tailTrace_1704758 : CollatzResearch.WordTrace tailWord_1704758 prefixEnd_1704758 875360253597546360184967 := by
  unfold tailWord_1704758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886102022372524395744683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41451754905306926887943285 3886102022372524395744683)
  ·
    refine ⟨5829153033558786593617025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3886102022372524395744683 5829153033558786593617025)
    ·
      refine ⟨4371864775169089945212769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5829153033558786593617025 4371864775169089945212769)
      ·
        refine ⟨3278898581376817458909577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4371864775169089945212769 3278898581376817458909577)
        ·
          refine ⟨2459173936032613094182183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3278898581376817458909577 2459173936032613094182183)
          ·
            refine ⟨3688760904048919641273275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459173936032613094182183 3688760904048919641273275)
            ·
              refine ⟨5533141356073379461909913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688760904048919641273275 5533141356073379461909913)
              ·
                refine ⟨4149856017055034596432435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533141356073379461909913 4149856017055034596432435)
                ·
                  refine ⟨6224784025582551894648653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149856017055034596432435 6224784025582551894648653)
                  ·
                    refine ⟨2334294009593456960493245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6224784025582551894648653 2334294009593456960493245)
                    ·
                      refine ⟨875360253597546360184967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334294009593456960493245 875360253597546360184967)
                      ·
                        rfl

theorem cell23_1704758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1704758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704758 prefixEnd_1704758 := by exact prefixLift 1704758
  have htrace : WordTrace (prefixWord ++ tailWord_1704758) baseStart_1704758 baseEnd_1704758 := by
    simpa [prefixWord, tailWord_1704758, baseEnd_1704758] using wordTrace_append hprefix tailTrace_1704758
  have hstable : (prefixWord ++ tailWord_1704758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704758).length < 2 ^ (prefixWord ++ tailWord_1704758).sum := by decide
  have hdescent : baseEnd_1704758 < baseStart_1704758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704794 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1704794 : Nat := 118140960795 + 1704794 * 2 ^ 59
def prefixEnd_1704794 : Nat := 4983230072969 + 3 ^ 40 * 1704794 * 2
def baseEnd_1704794 : Nat := 875378738901108219334801

theorem tailTrace_1704794 : CollatzResearch.WordTrace tailWord_1704794 prefixEnd_1704794 875378738901108219334801 := by
  unfold tailWord_1704794
  simp only [CollatzResearch.WordTrace]
  refine ⟨15544736346457492120056359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41452630257219978986816957 15544736346457492120056359)
  ·
    refine ⟨23317104519686238180084539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15544736346457492120056359 23317104519686238180084539)
    ·
      refine ⟨34975656779529357270126809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23317104519686238180084539 34975656779529357270126809)
      ·
        refine ⟨26231742584647017952595107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34975656779529357270126809 26231742584647017952595107)
        ·
          refine ⟨39347613876970526928892661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26231742584647017952595107 39347613876970526928892661)
          ·
            refine ⟨3688838800965986899583687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39347613876970526928892661 3688838800965986899583687)
            ·
              refine ⟨5533258201448980349375531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688838800965986899583687 5533258201448980349375531)
              ·
                refine ⟨8299887302173470524063297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533258201448980349375531 8299887302173470524063297)
                ·
                  refine ⟨6224915476630102893047473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8299887302173470524063297 6224915476630102893047473)
                  ·
                    refine ⟨4668686607472577169785605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6224915476630102893047473 4668686607472577169785605)
                    ·
                      refine ⟨875378738901108219334801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4668686607472577169785605 875378738901108219334801)
                      ·
                        rfl

theorem cell23_1704794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1704794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704794 prefixEnd_1704794 := by exact prefixLift 1704794
  have htrace : WordTrace (prefixWord ++ tailWord_1704794) baseStart_1704794 baseEnd_1704794 := by
    simpa [prefixWord, tailWord_1704794, baseEnd_1704794] using wordTrace_append hprefix tailTrace_1704794
  have hstable : (prefixWord ++ tailWord_1704794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704794).length < 2 ^ (prefixWord ++ tailWord_1704794).sum := by decide
  have hdescent : baseEnd_1704794 < baseStart_1704794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704804 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 7]
def baseStart_1704804 : Nat := 118140960795 + 1704804 * 2 ^ 59
def prefixEnd_1704804 : Nat := 4983230072969 + 3 ^ 40 * 1704804 * 2
def baseEnd_1704804 : Nat := 97264874856405908912195

theorem tailTrace_1704804 : CollatzResearch.WordTrace tailWord_1704804 prefixEnd_1704804 97264874856405908912195 := by
  unfold tailWord_1704804
  simp only [CollatzResearch.WordTrace]
  refine ⟨31089655057896870094044733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41452873410529160125392977 31089655057896870094044733)
  ·
    refine ⟨11658620646711326285266775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31089655057896870094044733 11658620646711326285266775)
    ·
      refine ⟨17487930970066989427900163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11658620646711326285266775 17487930970066989427900163)
      ·
        refine ⟨26231896455100484141850245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17487930970066989427900163 26231896455100484141850245)
        ·
          refine ⟨4918480585331340776596921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26231896455100484141850245 4918480585331340776596921)
          ·
            refine ⟨3688860438998505582447691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4918480585331340776596921 3688860438998505582447691)
            ·
              refine ⟨5533290658497758373671537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688860438998505582447691 5533290658497758373671537)
              ·
                refine ⟨4149967993873318780253653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533290658497758373671537 4149967993873318780253653)
                ·
                  refine ⟨97264874856405908912195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4149967993873318780253653 97264874856405908912195)
                  ·
                    rfl

theorem cell23_1704804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_1704804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704804 prefixEnd_1704804 := by exact prefixLift 1704804
  have htrace : WordTrace (prefixWord ++ tailWord_1704804) baseStart_1704804 baseEnd_1704804 := by
    simpa [prefixWord, tailWord_1704804, baseEnd_1704804] using wordTrace_append hprefix tailTrace_1704804
  have hstable : (prefixWord ++ tailWord_1704804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704804).length < 2 ^ (prefixWord ++ tailWord_1704804).sum := by decide
  have hdescent : baseEnd_1704804 < baseStart_1704804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704821 : List Nat := [1, 3, 4, 1, 1, 2, 1, 5, 5]
def baseStart_1704821 : Nat := 118140960795 + 1704821 * 2 ^ 59
def prefixEnd_1704821 : Nat := 4983230072969 + 3 ^ 40 * 1704821 * 2
def baseEnd_1704821 : Nat := 97265844764308845966353

theorem tailTrace_1704821 : CollatzResearch.WordTrace tailWord_1704821 prefixEnd_1704821 97265844764308845966353 := by
  unfold tailWord_1704821
  simp only [CollatzResearch.WordTrace]
  refine ⟨62179930156732152091458317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41453286771154768060972211 62179930156732152091458317)
  ·
    refine ⟨23317473808774557034296869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62179930156732152091458317 23317473808774557034296869)
    ·
      refine ⟨4372026339145229443930663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23317473808774557034296869 4372026339145229443930663)
      ·
        refine ⟨6558039508717844165895995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372026339145229443930663 6558039508717844165895995)
        ·
          refine ⟨9837059263076766248843993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558039508717844165895995 9837059263076766248843993)
          ·
            refine ⟨7377794447307574686632995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9837059263076766248843993 7377794447307574686632995)
            ·
              refine ⟨11066691670961362029949493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377794447307574686632995 11066691670961362029949493)
              ·
                refine ⟨1037502344152627690307765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11066691670961362029949493 1037502344152627690307765)
                ·
                  refine ⟨97265844764308845966353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037502344152627690307765 97265844764308845966353)
                  ·
                    rfl

theorem cell23_1704821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 5].length) (baseStart_1704821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704821 prefixEnd_1704821 := by exact prefixLift 1704821
  have htrace : WordTrace (prefixWord ++ tailWord_1704821) baseStart_1704821 baseEnd_1704821 := by
    simpa [prefixWord, tailWord_1704821, baseEnd_1704821] using wordTrace_append hprefix tailTrace_1704821
  have hstable : (prefixWord ++ tailWord_1704821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704821).length < 2 ^ (prefixWord ++ tailWord_1704821).sum := by decide
  have hdescent : baseEnd_1704821 < baseStart_1704821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704824 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 7, 2]
def baseStart_1704824 : Nat := 118140960795 + 1704824 * 2 ^ 59
def prefixEnd_1704824 : Nat := 4983230072969 + 3 ^ 40 * 1704824 * 2
def baseEnd_1704824 : Nat := 875394143320743101959663

theorem tailTrace_1704824 : CollatzResearch.WordTrace tailWord_1704824 prefixEnd_1704824 875394143320743101959663 := by
  unfold tailWord_1704824
  simp only [CollatzResearch.WordTrace]
  refine ⟨31090019787860641801908763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41453359717147522402545017 31090019787860641801908763)
  ·
    refine ⟨46635029681790962702863145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31090019787860641801908763 46635029681790962702863145)
    ·
      refine ⟨34976272261343222027147359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46635029681790962702863145 34976272261343222027147359)
      ·
        refine ⟨52464408392014833040721039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34976272261343222027147359 52464408392014833040721039)
        ·
          refine ⟨78696612588022249561081559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52464408392014833040721039 78696612588022249561081559)
          ·
            refine ⟨118044918882033374341622339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78696612588022249561081559 118044918882033374341622339)
            ·
              refine ⟨177067378323050061512433509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118044918882033374341622339 177067378323050061512433509)
              ·
                refine ⟨33200133435571886533581283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177067378323050061512433509 33200133435571886533581283)
                ·
                  refine ⟨49800200153357829800371925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33200133435571886533581283 49800200153357829800371925)
                  ·
                    refine ⟨1167192191094324135946217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49800200153357829800371925 1167192191094324135946217)
                    ·
                      refine ⟨875394143320743101959663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167192191094324135946217 875394143320743101959663)
                      ·
                        rfl

theorem cell23_1704824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_1704824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704824 prefixEnd_1704824 := by exact prefixLift 1704824
  have htrace : WordTrace (prefixWord ++ tailWord_1704824) baseStart_1704824 baseEnd_1704824 := by
    simpa [prefixWord, tailWord_1704824, baseEnd_1704824] using wordTrace_append hprefix tailTrace_1704824
  have hstable : (prefixWord ++ tailWord_1704824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704824).length < 2 ^ (prefixWord ++ tailWord_1704824).sum := by decide
  have hdescent : baseEnd_1704824 < baseStart_1704824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704827 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_1704827 : Nat := 118140960795 + 1704827 * 2 ^ 59
def prefixEnd_1704827 : Nat := 4983230072969 + 3 ^ 40 * 1704827 * 2
def baseEnd_1704827 : Nat := 875395683762706590222149

theorem tailTrace_1704827 : CollatzResearch.WordTrace tailWord_1704827 prefixEnd_1704827 875395683762706590222149 := by
  unfold tailWord_1704827
  simp only [CollatzResearch.WordTrace]
  refine ⟨62180148994710415116176735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41453432663140276744117823 62180148994710415116176735)
  ·
    refine ⟨93270223492065622674265103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62180148994710415116176735 93270223492065622674265103)
    ·
      refine ⟨139905335238098434011397655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93270223492065622674265103 139905335238098434011397655)
      ·
        refine ⟨209858002857147651017096483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139905335238098434011397655 209858002857147651017096483)
        ·
          refine ⟨314787004285721476525644725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209858002857147651017096483 314787004285721476525644725)
          ·
            refine ⟨29511281651786388424279193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 314787004285721476525644725 29511281651786388424279193)
            ·
              refine ⟨22133461238839791318209395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29511281651786388424279193 22133461238839791318209395)
              ·
                refine ⟨33200191858259686977314093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22133461238839791318209395 33200191858259686977314093)
                ·
                  refine ⟨12450071946847382616492785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33200191858259686977314093 12450071946847382616492785)
                  ·
                    refine ⟨9337553960135536962369589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12450071946847382616492785 9337553960135536962369589)
                    ·
                      refine ⟨875395683762706590222149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9337553960135536962369589 875395683762706590222149)
                      ·
                        rfl

theorem cell23_1704827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_1704827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704827 prefixEnd_1704827 := by exact prefixLift 1704827
  have htrace : WordTrace (prefixWord ++ tailWord_1704827) baseStart_1704827 baseEnd_1704827 := by
    simpa [prefixWord, tailWord_1704827, baseEnd_1704827] using wordTrace_append hprefix tailTrace_1704827
  have hstable : (prefixWord ++ tailWord_1704827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704827).length < 2 ^ (prefixWord ++ tailWord_1704827).sum := by decide
  have hdescent : baseEnd_1704827 < baseStart_1704827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704894 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1704894 : Nat := 118140960795 + 1704894 * 2 ^ 59
def prefixEnd_1704894 : Nat := 4983230072969 + 3 ^ 40 * 1704894 * 2
def baseEnd_1704894 : Nat := 97270009662950869787149

theorem tailTrace_1704894 : CollatzResearch.WordTrace tailWord_1704894 prefixEnd_1704894 97270009662950869787149 := by
  unfold tailWord_1704894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772824085683460694858217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41455061790311790372577157 7772824085683460694858217)
  ·
    refine ⟨5829618064262595521143663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7772824085683460694858217 5829618064262595521143663)
    ·
      refine ⟨8744427096393893281715495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5829618064262595521143663 8744427096393893281715495)
      ·
        refine ⟨13116640644590839922573243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744427096393893281715495 13116640644590839922573243)
        ·
          refine ⟨19674960966886259883859865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13116640644590839922573243 19674960966886259883859865)
          ·
            refine ⟨14756220725164694912894899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19674960966886259883859865 14756220725164694912894899)
            ·
              refine ⟨22134331087747042369342349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14756220725164694912894899 22134331087747042369342349)
              ·
                refine ⟨8300374157905140888503381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22134331087747042369342349 8300374157905140888503381)
                ·
                  refine ⟨97270009662950869787149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8300374157905140888503381 97270009662950869787149)
                  ·
                    rfl

theorem cell23_1704894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1704894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704894 prefixEnd_1704894 := by exact prefixLift 1704894
  have htrace : WordTrace (prefixWord ++ tailWord_1704894) baseStart_1704894 baseEnd_1704894 := by
    simpa [prefixWord, tailWord_1704894, baseEnd_1704894] using wordTrace_append hprefix tailTrace_1704894
  have hstable : (prefixWord ++ tailWord_1704894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704894).length < 2 ^ (prefixWord ++ tailWord_1704894).sum := by decide
  have hdescent : baseEnd_1704894 < baseStart_1704894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704911 : List Nat := [1, 1, 2, 1, 1, 6, 4, 1, 6]
def baseStart_1704911 : Nat := 118140960795 + 1704911 * 2 ^ 59
def prefixEnd_1704911 : Nat := 4983230072969 + 3 ^ 40 * 1704911 * 2
def baseEnd_1704911 : Nat := 97270979570853806841307

theorem tailTrace_1704911 : CollatzResearch.WordTrace tailWord_1704911 prefixEnd_1704911 97270979570853806841307 := by
  unfold tailWord_1704911
  simp only [CollatzResearch.WordTrace]
  refine ⟨62183212726406097462234587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41455475150937398308156391 62183212726406097462234587)
  ·
    refine ⟨93274819089609146193351881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62183212726406097462234587 93274819089609146193351881)
    ·
      refine ⟨69956114317206859645013911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93274819089609146193351881 69956114317206859645013911)
      ·
        refine ⟨104934171475810289467520867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69956114317206859645013911 104934171475810289467520867)
        ·
          refine ⟨157401257213715434201281301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104934171475810289467520867 157401257213715434201281301)
          ·
            refine ⟨7378183931892910978185061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157401257213715434201281301 7378183931892910978185061)
            ·
              refine ⟨1383409487229920808409699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7378183931892910978185061 1383409487229920808409699)
              ·
                refine ⟨2075114230844881212614549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383409487229920808409699 2075114230844881212614549)
                ·
                  refine ⟨97270979570853806841307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2075114230844881212614549 97270979570853806841307)
                  ·
                    rfl

theorem cell23_1704911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 6].length) (baseStart_1704911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704911 prefixEnd_1704911 := by exact prefixLift 1704911
  have htrace : WordTrace (prefixWord ++ tailWord_1704911) baseStart_1704911 baseEnd_1704911 := by
    simpa [prefixWord, tailWord_1704911, baseEnd_1704911] using wordTrace_append hprefix tailTrace_1704911
  have hstable : (prefixWord ++ tailWord_1704911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704911).length < 2 ^ (prefixWord ++ tailWord_1704911).sum := by decide
  have hdescent : baseEnd_1704911 < baseStart_1704911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704961 : List Nat := [1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 4]
def baseStart_1704961 : Nat := 118140960795 + 1704961 * 2 ^ 59
def prefixEnd_1704961 : Nat := 4983230072969 + 3 ^ 40 * 1704961 * 2
def baseEnd_1704961 : Nat := 875464490170409065946533

theorem tailTrace_1704961 : CollatzResearch.WordTrace tailWord_1704961 prefixEnd_1704961 875464490170409065946533 := by
  unfold tailWord_1704961
  simp only [CollatzResearch.WordTrace]
  refine ⟨62185036376224956001554737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41456690917483304001036491 62185036376224956001554737)
  ·
    refine ⟨46638777282168717001166053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62185036376224956001554737 46638777282168717001166053)
    ·
      refine ⟨8744770740406634437718635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46638777282168717001166053 8744770740406634437718635)
      ·
        refine ⟨13117156110609951656577953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744770740406634437718635 13117156110609951656577953)
        ·
          refine ⟨9837867082957463742433465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13117156110609951656577953 9837867082957463742433465)
          ·
            refine ⟨7378400312218097806825099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9837867082957463742433465 7378400312218097806825099)
            ·
              refine ⟨11067600468327146710237649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378400312218097806825099 11067600468327146710237649)
              ·
                refine ⟨8300700351245360032678237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11067600468327146710237649 8300700351245360032678237)
                ·
                  refine ⟨3112762631717010012254339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8300700351245360032678237 3112762631717010012254339)
                  ·
                    refine ⟨4669143947575515018381509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3112762631717010012254339 4669143947575515018381509)
                    ·
                      refine ⟨875464490170409065946533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4669143947575515018381509 875464490170409065946533)
                      ·
                        rfl

theorem cell23_1704961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_1704961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704961 prefixEnd_1704961 := by exact prefixLift 1704961
  have htrace : WordTrace (prefixWord ++ tailWord_1704961) baseStart_1704961 baseEnd_1704961 := by
    simpa [prefixWord, tailWord_1704961, baseEnd_1704961] using wordTrace_append hprefix tailTrace_1704961
  have hstable : (prefixWord ++ tailWord_1704961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704961).length < 2 ^ (prefixWord ++ tailWord_1704961).sum := by decide
  have hdescent : baseEnd_1704961 < baseStart_1704961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704971 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 1, 6]
def baseStart_1704971 : Nat := 118140960795 + 1704971 * 2 ^ 59
def prefixEnd_1704971 : Nat := 4983230072969 + 3 ^ 40 * 1704971 * 2
def baseEnd_1704971 : Nat := 291823208325651342273829

theorem tailTrace_1704971 : CollatzResearch.WordTrace tailWord_1704971 prefixEnd_1704971 291823208325651342273829 := by
  unfold tailWord_1704971
  simp only [CollatzResearch.WordTrace]
  refine ⟨62185401106188727709418767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41456934070792485139612511 62185401106188727709418767)
  ·
    refine ⟨93278101659283091564128151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62185401106188727709418767 93278101659283091564128151)
    ·
      refine ⟨139917152488924637346192227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93278101659283091564128151 139917152488924637346192227)
      ·
        refine ⟨209875728733386956019288341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139917152488924637346192227 209875728733386956019288341)
        ·
          refine ⟨9837924784377513563404141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209875728733386956019288341 9837924784377513563404141)
          ·
            refine ⟨3689221794141567586276553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9837924784377513563404141 3689221794141567586276553)
            ·
              refine ⟨2766916345606175689707415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689221794141567586276553 2766916345606175689707415)
              ·
                refine ⟨4150374518409263534561123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766916345606175689707415 4150374518409263534561123)
                ·
                  refine ⟨6225561777613895301841685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150374518409263534561123 6225561777613895301841685)
                  ·
                    refine ⟨291823208325651342273829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6225561777613895301841685 291823208325651342273829)
                    ·
                      rfl

theorem cell23_1704971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 6].length) (baseStart_1704971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704971 prefixEnd_1704971 := by exact prefixLift 1704971
  have htrace : WordTrace (prefixWord ++ tailWord_1704971) baseStart_1704971 baseEnd_1704971 := by
    simpa [prefixWord, tailWord_1704971, baseEnd_1704971] using wordTrace_append hprefix tailTrace_1704971
  have hstable : (prefixWord ++ tailWord_1704971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704971).length < 2 ^ (prefixWord ++ tailWord_1704971).sum := by decide
  have hdescent : baseEnd_1704971 < baseStart_1704971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704991 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1704991 : Nat := 118140960795 + 1704991 * 2 ^ 59
def prefixEnd_1704991 : Nat := 4983230072969 + 3 ^ 40 * 1704991 * 2
def baseEnd_1704991 : Nat := 875479894590043948571395

theorem tailTrace_1704991 : CollatzResearch.WordTrace tailWord_1704991 prefixEnd_1704991 875479894590043948571395 := by
  unfold tailWord_1704991
  simp only [CollatzResearch.WordTrace]
  refine ⟨62186130566116271125146827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41457420377410847416764551 62186130566116271125146827)
  ·
    refine ⟨93279195849174406687720241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62186130566116271125146827 93279195849174406687720241)
    ·
      refine ⟨69959396886880805015790181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93279195849174406687720241 69959396886880805015790181)
      ·
        refine ⟨13117386916290150940460659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69959396886880805015790181 13117386916290150940460659)
        ·
          refine ⟨19676080374435226410690989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13117386916290150940460659 19676080374435226410690989)
          ·
            refine ⟨7378530140413209904009121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19676080374435226410690989 7378530140413209904009121)
            ·
              refine ⟨5533897605309907428006841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7378530140413209904009121 5533897605309907428006841)
              ·
                refine ⟨4150423203982430571005131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5533897605309907428006841 4150423203982430571005131)
                ·
                  refine ⟨6225634805973645856507697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150423203982430571005131 6225634805973645856507697)
                  ·
                    refine ⟨4669226104480234392380773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225634805973645856507697 4669226104480234392380773)
                    ·
                      refine ⟨875479894590043948571395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4669226104480234392380773 875479894590043948571395)
                      ·
                        rfl

theorem cell23_1704991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1704991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704991 prefixEnd_1704991 := by exact prefixLift 1704991
  have htrace : WordTrace (prefixWord ++ tailWord_1704991) baseStart_1704991 baseEnd_1704991 := by
    simpa [prefixWord, tailWord_1704991, baseEnd_1704991] using wordTrace_append hprefix tailTrace_1704991
  have hstable : (prefixWord ++ tailWord_1704991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704991).length < 2 ^ (prefixWord ++ tailWord_1704991).sum := by decide
  have hdescent : baseEnd_1704991 < baseStart_1704991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704992 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 1, 5]
def baseStart_1704992 : Nat := 118140960795 + 1704992 * 2 ^ 59
def prefixEnd_1704992 : Nat := 4983230072969 + 3 ^ 40 * 1704992 * 2
def baseEnd_1704992 : Nat := 291826802690232814886297

theorem tailTrace_1704992 : CollatzResearch.WordTrace tailWord_1704992 prefixEnd_1704992 291826802690232814886297 := by
  unfold tailWord_1704992
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093083519556324147966615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41457444692741765530622153 31093083519556324147966615)
  ·
    refine ⟨46639625279334486221949923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31093083519556324147966615 46639625279334486221949923)
    ·
      refine ⟨69959437919001729332924885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46639625279334486221949923 69959437919001729332924885)
      ·
        refine ⟨1639674326226603031240427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 69959437919001729332924885 1639674326226603031240427)
        ·
          refine ⟨2459511489339904546860641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639674326226603031240427 2459511489339904546860641)
          ·
            refine ⟨1844633617004928410145481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459511489339904546860641 1844633617004928410145481)
            ·
              refine ⟨1383475212753696307609111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844633617004928410145481 1383475212753696307609111)
              ·
                refine ⟨2075212819130544461413667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383475212753696307609111 2075212819130544461413667)
                ·
                  refine ⟨3112819228695816692120501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075212819130544461413667 3112819228695816692120501)
                  ·
                    refine ⟨291826802690232814886297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3112819228695816692120501 291826802690232814886297)
                    ·
                      rfl

theorem cell23_1704992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 5].length) (baseStart_1704992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704992 prefixEnd_1704992 := by exact prefixLift 1704992
  have htrace : WordTrace (prefixWord ++ tailWord_1704992) baseStart_1704992 baseEnd_1704992 := by
    simpa [prefixWord, tailWord_1704992, baseEnd_1704992] using wordTrace_append hprefix tailTrace_1704992
  have hstable : (prefixWord ++ tailWord_1704992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704992).length < 2 ^ (prefixWord ++ tailWord_1704992).sum := by decide
  have hdescent : baseEnd_1704992 < baseStart_1704992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1704995 : List Nat := [1, 1, 1, 4, 3, 4, 2, 1, 1, 1, 4]
def baseStart_1704995 : Nat := 118140960795 + 1704995 * 2 ^ 59
def prefixEnd_1704995 : Nat := 4983230072969 + 3 ^ 40 * 1704995 * 2
def baseEnd_1704995 : Nat := 875481948512661932921377

theorem tailTrace_1704995 : CollatzResearch.WordTrace tailWord_1704995 prefixEnd_1704995 875481948512661932921377 := by
  unfold tailWord_1704995
  simp only [CollatzResearch.WordTrace]
  refine ⟨62186276458101779808292439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41457517638734519872194959 62186276458101779808292439)
  ·
    refine ⟨93279414687152669712438659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62186276458101779808292439 93279414687152669712438659)
    ·
      refine ⟨139919122030729004568657989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93279414687152669712438659 139919122030729004568657989)
      ·
        refine ⟨26234835380761688356623373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139919122030729004568657989 26234835380761688356623373)
        ·
          refine ⟨9838063267785633133733765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26234835380761688356623373 9838063267785633133733765)
          ·
            refine ⟨1844636862709806212575081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9838063267785633133733765 1844636862709806212575081)
            ·
              refine ⟨1383477647032354659431311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844636862709806212575081 1383477647032354659431311)
              ·
                refine ⟨2075216470548531989146967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383477647032354659431311 2075216470548531989146967)
                ·
                  refine ⟨3112824705822797983720451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075216470548531989146967 3112824705822797983720451)
                  ·
                    refine ⟨4669237058734196975580677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3112824705822797983720451 4669237058734196975580677)
                    ·
                      refine ⟨875481948512661932921377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4669237058734196975580677 875481948512661932921377)
                      ·
                        rfl

theorem cell23_1704995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 1, 1, 4].length) (baseStart_1704995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1704995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1704995 prefixEnd_1704995 := by exact prefixLift 1704995
  have htrace : WordTrace (prefixWord ++ tailWord_1704995) baseStart_1704995 baseEnd_1704995 := by
    simpa [prefixWord, tailWord_1704995, baseEnd_1704995] using wordTrace_append hprefix tailTrace_1704995
  have hstable : (prefixWord ++ tailWord_1704995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1704995).length < 2 ^ (prefixWord ++ tailWord_1704995).sum := by decide
  have hdescent : baseEnd_1704995 < baseStart_1704995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1704995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705012 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1705012 : Nat := 118140960795 + 1705012 * 2 ^ 59
def prefixEnd_1705012 : Nat := 4983230072969 + 3 ^ 40 * 1705012 * 2
def baseEnd_1705012 : Nat := 875490677683788366408799

theorem tailTrace_1705012 : CollatzResearch.WordTrace tailWord_1705012 prefixEnd_1705012 875490677683788366408799 := by
  unfold tailWord_1705012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093448249520095855830645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41457930999360127807774193 31093448249520095855830645)
  ·
    refine ⟨2915010773392508986484123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31093448249520095855830645 2915010773392508986484123)
    ·
      refine ⟨4372516160088763479726185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915010773392508986484123 4372516160088763479726185)
      ·
        refine ⟨3279387120066572609794639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372516160088763479726185 3279387120066572609794639)
        ·
          refine ⟨4919080680099858914691959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279387120066572609794639 4919080680099858914691959)
          ·
            refine ⟨7378621020149788372037939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919080680099858914691959 7378621020149788372037939)
            ·
              refine ⟨11067931530224682558056909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378621020149788372037939 11067931530224682558056909)
              ·
                refine ⟨4150474323834255959271341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11067931530224682558056909 4150474323834255959271341)
                ·
                  refine ⟨1556427871437845984726753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4150474323834255959271341 1556427871437845984726753)
                  ·
                    refine ⟨1167320903578384488545065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1556427871437845984726753 1167320903578384488545065)
                    ·
                      refine ⟨875490677683788366408799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167320903578384488545065 875490677683788366408799)
                      ·
                        rfl

theorem cell23_1705012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1705012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705012 prefixEnd_1705012 := by exact prefixLift 1705012
  have htrace : WordTrace (prefixWord ++ tailWord_1705012) baseStart_1705012 baseEnd_1705012 := by
    simpa [prefixWord, tailWord_1705012, baseEnd_1705012] using wordTrace_append hprefix tailTrace_1705012
  have hstable : (prefixWord ++ tailWord_1705012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705012).length < 2 ^ (prefixWord ++ tailWord_1705012).sum := by decide
  have hdescent : baseEnd_1705012 < baseStart_1705012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705022 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1705022 : Nat := 118140960795 + 1705022 * 2 ^ 59
def prefixEnd_1705022 : Nat := 4983230072969 + 3 ^ 40 * 1705022 * 2
def baseEnd_1705022 : Nat := 291831937496777775761251

theorem tailTrace_1705022 : CollatzResearch.WordTrace tailWord_1705022 prefixEnd_1705022 291831937496777775761251 := by
  unfold tailWord_1705022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7773407653625495427440665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41458174152669308946350213 7773407653625495427440665)
  ·
    refine ⟨5830055740219121570580499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7773407653625495427440665 5830055740219121570580499)
    ·
      refine ⟨8745083610328682355870749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5830055740219121570580499 8745083610328682355870749)
      ·
        refine ⟨3279406353873255883451531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8745083610328682355870749 3279406353873255883451531)
        ·
          refine ⟨4919109530809883825177297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279406353873255883451531 4919109530809883825177297)
          ·
            refine ⟨3689332148107412868882973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919109530809883825177297 3689332148107412868882973)
            ·
              refine ⟨1383499555540279825831115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3689332148107412868882973 1383499555540279825831115)
              ·
                refine ⟨2075249333310419738746673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383499555540279825831115 2075249333310419738746673)
                ·
                  refine ⟨1556436999982814804060005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075249333310419738746673 1556436999982814804060005)
                  ·
                    refine ⟨291831937496777775761251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556436999982814804060005 291831937496777775761251)
                    ·
                      rfl

theorem cell23_1705022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1705022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705022 prefixEnd_1705022 := by exact prefixLift 1705022
  have htrace : WordTrace (prefixWord ++ tailWord_1705022) baseStart_1705022 baseEnd_1705022 := by
    simpa [prefixWord, tailWord_1705022, baseEnd_1705022] using wordTrace_append hprefix tailTrace_1705022
  have hstable : (prefixWord ++ tailWord_1705022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705022).length < 2 ^ (prefixWord ++ tailWord_1705022).sum := by decide
  have hdescent : baseEnd_1705022 < baseStart_1705022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705025 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1705025 : Nat := 118140960795 + 1705025 * 2 ^ 59
def prefixEnd_1705025 : Nat := 4983230072969 + 3 ^ 40 * 1705025 * 2
def baseEnd_1705025 : Nat := 875497352932296815546239

theorem tailTrace_1705025 : CollatzResearch.WordTrace tailWord_1705025 prefixEnd_1705025 875497352932296815546239 := by
  unfold tailWord_1705025
  simp only [CollatzResearch.WordTrace]
  refine ⟨62187370647993094931884529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41458247098662063287923019 62187370647993094931884529)
  ·
    refine ⟨46640527985994821198913397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62187370647993094931884529 46640527985994821198913397)
    ·
      refine ⟨4372549498687014487398131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46640527985994821198913397 4372549498687014487398131)
      ·
        refine ⟨6558824248030521731097197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4372549498687014487398131 6558824248030521731097197)
        ·
          refine ⟨2459559093011445649161449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6558824248030521731097197 2459559093011445649161449)
          ·
            refine ⟨1844669319758584236871087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2459559093011445649161449 1844669319758584236871087)
            ·
              refine ⟨2767003979637876355306631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844669319758584236871087 2767003979637876355306631)
              ·
                refine ⟨4150505969456814532959947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767003979637876355306631 4150505969456814532959947)
                ·
                  refine ⟨6225758954185221799439921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150505969456814532959947 6225758954185221799439921)
                  ·
                    refine ⟨4669319215638916349579941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6225758954185221799439921 4669319215638916349579941)
                    ·
                      refine ⟨875497352932296815546239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4669319215638916349579941 875497352932296815546239)
                      ·
                        rfl

theorem cell23_1705025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1705025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705025 prefixEnd_1705025 := by exact prefixLift 1705025
  have htrace : WordTrace (prefixWord ++ tailWord_1705025) baseStart_1705025 baseEnd_1705025 := by
    simpa [prefixWord, tailWord_1705025, baseEnd_1705025] using wordTrace_append hprefix tailTrace_1705025
  have hstable : (prefixWord ++ tailWord_1705025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705025).length < 2 ^ (prefixWord ++ tailWord_1705025).sum := by decide
  have hdescent : baseEnd_1705025 < baseStart_1705025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705071 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_1705071 : Nat := 118140960795 + 1705071 * 2 ^ 59
def prefixEnd_1705071 : Nat := 4983230072969 + 3 ^ 40 * 1705071 * 2
def baseEnd_1705071 : Nat := 875520973042403635571027

theorem tailTrace_1705071 : CollatzResearch.WordTrace tailWord_1705071 prefixEnd_1705071 875520973042403635571027 := by
  unfold tailWord_1705071
  simp only [CollatzResearch.WordTrace]
  refine ⟨62189048405826444788059067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41459365603884296525372711 62189048405826444788059067)
  ·
    refine ⟨93283572608739667182088601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62189048405826444788059067 93283572608739667182088601)
    ·
      refine ⟨69962679456554750386566451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93283572608739667182088601 69962679456554750386566451)
      ·
        refine ⟨104944019184832125579849677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69962679456554750386566451 104944019184832125579849677)
        ·
          refine ⟨39354007194312047092443629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104944019184832125579849677 39354007194312047092443629)
          ·
            refine ⟨14757752697867017659666361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39354007194312047092443629 14757752697867017659666361)
            ·
              refine ⟨11068314523400263244749771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14757752697867017659666361 11068314523400263244749771)
              ·
                refine ⟨16602471785100394867124657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11068314523400263244749771 16602471785100394867124657)
                ·
                  refine ⟨12451853838825296150343493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16602471785100394867124657 12451853838825296150343493)
                  ·
                    refine ⟨2334722594779743028189405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12451853838825296150343493 2334722594779743028189405)
                    ·
                      refine ⟨875520973042403635571027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334722594779743028189405 875520973042403635571027)
                      ·
                        rfl

theorem cell23_1705071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_1705071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705071 prefixEnd_1705071 := by exact prefixLift 1705071
  have htrace : WordTrace (prefixWord ++ tailWord_1705071) baseStart_1705071 baseEnd_1705071 := by
    simpa [prefixWord, tailWord_1705071, baseEnd_1705071] using wordTrace_append hprefix tailTrace_1705071
  have hstable : (prefixWord ++ tailWord_1705071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705071).length < 2 ^ (prefixWord ++ tailWord_1705071).sum := by decide
  have hdescent : baseEnd_1705071 < baseStart_1705071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705119 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1705119 : Nat := 118140960795 + 1705119 * 2 ^ 59
def prefixEnd_1705119 : Nat := 4983230072969 + 3 ^ 40 * 1705119 * 2
def baseEnd_1705119 : Nat := 875545620113819447770807

theorem tailTrace_1705119 : CollatzResearch.WordTrace tailWord_1705119 prefixEnd_1705119 875545620113819447770807 := by
  unfold tailWord_1705119
  simp only [CollatzResearch.WordTrace]
  refine ⟨62190799109652548985806411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41460532739768365990537607 62190799109652548985806411)
  ·
    refine ⟨93286198664478823478709617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62190799109652548985806411 93286198664478823478709617)
    ·
      refine ⟨69964648998359117609032213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93286198664478823478709617 69964648998359117609032213)
      ·
        refine ⟨3279592921798083637923385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69964648998359117609032213 3279592921798083637923385)
        ·
          refine ⟨2459694691348562728442539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279592921798083637923385 2459694691348562728442539)
          ·
            refine ⟨3689542037022844092663809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459694691348562728442539 3689542037022844092663809)
            ·
              refine ⟨2767156527767133069497857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689542037022844092663809 2767156527767133069497857)
              ·
                refine ⟨2075367395825349802123393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767156527767133069497857 2075367395825349802123393)
                ·
                  refine ⟨1556525546869012351592545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075367395825349802123393 1556525546869012351592545)
                  ·
                    refine ⟨1167394160151759263694409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1556525546869012351592545 1167394160151759263694409)
                    ·
                      refine ⟨875545620113819447770807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167394160151759263694409 875545620113819447770807)
                      ·
                        rfl

theorem cell23_1705119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1705119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705119 prefixEnd_1705119 := by exact prefixLift 1705119
  have htrace : WordTrace (prefixWord ++ tailWord_1705119) baseStart_1705119 baseEnd_1705119 := by
    simpa [prefixWord, tailWord_1705119, baseEnd_1705119] using wordTrace_append hprefix tailTrace_1705119
  have hstable : (prefixWord ++ tailWord_1705119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705119).length < 2 ^ (prefixWord ++ tailWord_1705119).sum := by decide
  have hdescent : baseEnd_1705119 < baseStart_1705119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705125 : List Nat := [1, 3, 1, 2, 1, 4, 4, 2, 5]
def baseStart_1705125 : Nat := 118140960795 + 1705125 * 2 ^ 59
def prefixEnd_1705125 : Nat := 4983230072969 + 3 ^ 40 * 1705125 * 2
def baseEnd_1705125 : Nat := 97283188999749602699531

theorem tailTrace_1705125 : CollatzResearch.WordTrace tailWord_1705125 prefixEnd_1705125 97283188999749602699531 := by
  unfold tailWord_1705125
  simp only [CollatzResearch.WordTrace]
  refine ⟨62191017947630812010524829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41460678631753874673683219 62191017947630812010524829)
  ·
    refine ⟨23321631730361554503946811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62191017947630812010524829 23321631730361554503946811)
    ·
      refine ⟨34982447595542331755920217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23321631730361554503946811 34982447595542331755920217)
      ·
        refine ⟨26236835696656748816940163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34982447595542331755920217 26236835696656748816940163)
        ·
          refine ⟨39355253544985123225410245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26236835696656748816940163 39355253544985123225410245)
          ·
            refine ⟨7379110039684710604764421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39355253544985123225410245 7379110039684710604764421)
            ·
              refine ⟨1383583132440883238393329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7379110039684710604764421 1383583132440883238393329)
              ·
                refine ⟨1037687349330662428794997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383583132440883238393329 1037687349330662428794997)
                ·
                  refine ⟨97283188999749602699531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1037687349330662428794997 97283188999749602699531)
                  ·
                    rfl

theorem cell23_1705125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_1705125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705125 prefixEnd_1705125 := by exact prefixLift 1705125
  have htrace : WordTrace (prefixWord ++ tailWord_1705125) baseStart_1705125 baseEnd_1705125 := by
    simpa [prefixWord, tailWord_1705125, baseEnd_1705125] using wordTrace_append hprefix tailTrace_1705125
  have hstable : (prefixWord ++ tailWord_1705125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705125).length < 2 ^ (prefixWord ++ tailWord_1705125).sum := by decide
  have hdescent : baseEnd_1705125 < baseStart_1705125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705142 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 7]
def baseStart_1705142 : Nat := 118140960795 + 1705142 * 2 ^ 59
def prefixEnd_1705142 : Nat := 4983230072969 + 3 ^ 40 * 1705142 * 2
def baseEnd_1705142 : Nat := 97284158907652539753689

theorem tailTrace_1705142 : CollatzResearch.WordTrace tailWord_1705142 prefixEnd_1705142 97284158907652539753689 := by
  unfold tailWord_1705142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886977374285576494618355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41461091992379482609262453 3886977374285576494618355)
  ·
    refine ⟨5830466061428364741927533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3886977374285576494618355 5830466061428364741927533)
    ·
      refine ⟨2186424773035636778222825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5830466061428364741927533 2186424773035636778222825)
      ·
        refine ⟨1639818579776727583667119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2186424773035636778222825 1639818579776727583667119)
        ·
          refine ⟨2459727869665091375500679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639818579776727583667119 2459727869665091375500679)
          ·
            refine ⟨3689591804497637063251019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459727869665091375500679 3689591804497637063251019)
            ·
              refine ⟨5534387706746455594876529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689591804497637063251019 5534387706746455594876529)
              ·
                refine ⟨4150790780059841696157397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534387706746455594876529 4150790780059841696157397)
                ·
                  refine ⟨97284158907652539753689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4150790780059841696157397 97284158907652539753689)
                  ·
                    rfl

theorem cell23_1705142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 7].length) (baseStart_1705142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705142 prefixEnd_1705142 := by exact prefixLift 1705142
  have htrace : WordTrace (prefixWord ++ tailWord_1705142) baseStart_1705142 baseEnd_1705142 := by
    simpa [prefixWord, tailWord_1705142, baseEnd_1705142] using wordTrace_append hprefix tailTrace_1705142
  have hstable : (prefixWord ++ tailWord_1705142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705142).length < 2 ^ (prefixWord ++ tailWord_1705142).sum := by decide
  have hdescent : baseEnd_1705142 < baseStart_1705142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705178 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1705178 : Nat := 118140960795 + 1705178 * 2 ^ 59
def prefixEnd_1705178 : Nat := 4983230072969 + 3 ^ 40 * 1705178 * 2
def baseEnd_1705178 : Nat := 875575915472434716933035

theorem tailTrace_1705178 : CollatzResearch.WordTrace tailWord_1705178 prefixEnd_1705178 875575915472434716933035 := by
  unfold tailWord_1705178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15548237754109700515551047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41461967344292534708136125 15548237754109700515551047)
  ·
    refine ⟨23322356631164550773326571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15548237754109700515551047 23322356631164550773326571)
    ·
      refine ⟨34983534946746826159989857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23322356631164550773326571 34983534946746826159989857)
      ·
        refine ⟨26237651210060119619992393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34983534946746826159989857 26237651210060119619992393)
        ·
          refine ⟨19678238407545089714994295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26237651210060119619992393 19678238407545089714994295)
          ·
            refine ⟨29517357611317634572491443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19678238407545089714994295 29517357611317634572491443)
            ·
              refine ⟨44276036416976451858737165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29517357611317634572491443 44276036416976451858737165)
              ·
                refine ⟨16603513656366169447026437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44276036416976451858737165 16603513656366169447026437)
                ·
                  refine ⟨3113158810568656771317457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16603513656366169447026437 3113158810568656771317457)
                  ·
                    refine ⟨2334869107926492578488093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3113158810568656771317457 2334869107926492578488093)
                    ·
                      refine ⟨875575915472434716933035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334869107926492578488093 875575915472434716933035)
                      ·
                        rfl

theorem cell23_1705178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1705178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705178 prefixEnd_1705178 := by exact prefixLift 1705178
  have htrace : WordTrace (prefixWord ++ tailWord_1705178) baseStart_1705178 baseEnd_1705178 := by
    simpa [prefixWord, tailWord_1705178, baseEnd_1705178] using wordTrace_append hprefix tailTrace_1705178
  have hstable : (prefixWord ++ tailWord_1705178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705178).length < 2 ^ (prefixWord ++ tailWord_1705178).sum := by decide
  have hdescent : baseEnd_1705178 < baseStart_1705178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705185 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 3, 4]
def baseStart_1705185 : Nat := 118140960795 + 1705185 * 2 ^ 59
def prefixEnd_1705185 : Nat := 4983230072969 + 3 ^ 40 * 1705185 * 2
def baseEnd_1705185 : Nat := 291859836612338729848501

theorem tailTrace_1705185 : CollatzResearch.WordTrace tailWord_1705185 prefixEnd_1705185 291859836612338729848501 := by
  unfold tailWord_1705185
  simp only [CollatzResearch.WordTrace]
  refine ⟨62193206327413442257709009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41462137551608961505139339 62193206327413442257709009)
  ·
    refine ⟨46644904745560081693281757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62193206327413442257709009 46644904745560081693281757)
    ·
      refine ⟨17491839279585030634980659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46644904745560081693281757 17491839279585030634980659)
      ·
        refine ⟨26237758919377545952470989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17491839279585030634980659 26237758919377545952470989)
        ·
          refine ⟨9839159594766579732176621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26237758919377545952470989 9839159594766579732176621)
          ·
            refine ⟨3689684848037467399566233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9839159594766579732176621 3689684848037467399566233)
            ·
              refine ⟨2767263636028100549674675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689684848037467399566233 2767263636028100549674675)
              ·
                refine ⟨4150895454042150824512013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767263636028100549674675 4150895454042150824512013)
                ·
                  refine ⟨1556585795265806559192005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4150895454042150824512013 1556585795265806559192005)
                  ·
                    refine ⟨291859836612338729848501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556585795265806559192005 291859836612338729848501)
                    ·
                      rfl

theorem cell23_1705185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_1705185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705185 prefixEnd_1705185 := by exact prefixLift 1705185
  have htrace : WordTrace (prefixWord ++ tailWord_1705185) baseStart_1705185 baseEnd_1705185 := by
    simpa [prefixWord, tailWord_1705185, baseEnd_1705185] using wordTrace_append hprefix tailTrace_1705185
  have hstable : (prefixWord ++ tailWord_1705185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705185).length < 2 ^ (prefixWord ++ tailWord_1705185).sum := by decide
  have hdescent : baseEnd_1705185 < baseStart_1705185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705198 : List Nat := [4, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_1705198 : Nat := 118140960795 + 1705198 * 2 ^ 59
def prefixEnd_1705198 : Nat := 4983230072969 + 3 ^ 40 * 1705198 * 2
def baseEnd_1705198 : Nat := 97287353898391626520327

theorem tailTrace_1705198 : CollatzResearch.WordTrace tailWord_1705198 prefixEnd_1705198 97287353898391626520327 := by
  unfold tailWord_1705198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774210059545793184741531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41462453650910896985288165 7774210059545793184741531)
  ·
    refine ⟨11661315089318689777112297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7774210059545793184741531 11661315089318689777112297)
    ·
      refine ⟨8745986316989017332834223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11661315089318689777112297 8745986316989017332834223)
      ·
        refine ⟨13118979475483525999251335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745986316989017332834223 13118979475483525999251335)
        ·
          refine ⟨19678469213225288998877003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13118979475483525999251335 19678469213225288998877003)
          ·
            refine ⟨29517703819837933498315505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19678469213225288998877003 29517703819837933498315505)
            ·
              refine ⟨22138277864878450123736629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29517703819837933498315505 22138277864878450123736629)
              ·
                refine ⟨2075463549832354699100309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22138277864878450123736629 2075463549832354699100309)
                ·
                  refine ⟨97287353898391626520327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2075463549832354699100309 97287353898391626520327)
                  ·
                    rfl

theorem cell23_1705198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_1705198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705198 prefixEnd_1705198 := by exact prefixLift 1705198
  have htrace : WordTrace (prefixWord ++ tailWord_1705198) baseStart_1705198 baseEnd_1705198 := by
    simpa [prefixWord, tailWord_1705198, baseEnd_1705198] using wordTrace_append hprefix tailTrace_1705198
  have hstable : (prefixWord ++ tailWord_1705198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705198).length < 2 ^ (prefixWord ++ tailWord_1705198).sum := by decide
  have hdescent : baseEnd_1705198 < baseStart_1705198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705201 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 6]
def baseStart_1705201 : Nat := 118140960795 + 1705201 * 2 ^ 59
def prefixEnd_1705201 : Nat := 4983230072969 + 3 ^ 40 * 1705201 * 2
def baseEnd_1705201 : Nat := 875587725527488126945429

theorem tailTrace_1705201 : CollatzResearch.WordTrace tailWord_1705201 prefixEnd_1705201 875587725527488126945429 := by
  unfold tailWord_1705201
  simp only [CollatzResearch.WordTrace]
  refine ⟨62193789895355476990291457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41462526596903651326860971 62193789895355476990291457)
  ·
    refine ⟨46645342421516607742718593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62193789895355476990291457 46645342421516607742718593)
    ·
      refine ⟨34984006816137455807038945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46645342421516607742718593 34984006816137455807038945)
      ·
        refine ⟨26238005112103091855279209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34984006816137455807038945 26238005112103091855279209)
        ·
          refine ⟨19678503834077318891459407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26238005112103091855279209 19678503834077318891459407)
          ·
            refine ⟨29517755751115978337189111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19678503834077318891459407 29517755751115978337189111)
            ·
              refine ⟨44276633626673967505783667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29517755751115978337189111 44276633626673967505783667)
              ·
                refine ⟨66414950440010951258675501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44276633626673967505783667 66414950440010951258675501)
                ·
                  refine ⟨24905606415004106722003313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66414950440010951258675501 24905606415004106722003313)
                  ·
                    refine ⟨18679204811253080041502485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24905606415004106722003313 18679204811253080041502485)
                    ·
                      refine ⟨875587725527488126945429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18679204811253080041502485 875587725527488126945429)
                      ·
                        rfl

theorem cell23_1705201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_1705201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705201 prefixEnd_1705201 := by exact prefixLift 1705201
  have htrace : WordTrace (prefixWord ++ tailWord_1705201) baseStart_1705201 baseEnd_1705201 := by
    simpa [prefixWord, tailWord_1705201, baseEnd_1705201] using wordTrace_append hprefix tailTrace_1705201
  have hstable : (prefixWord ++ tailWord_1705201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705201).length < 2 ^ (prefixWord ++ tailWord_1705201).sum := by decide
  have hdescent : baseEnd_1705201 < baseStart_1705201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705242 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_1705242 : Nat := 118140960795 + 1705242 * 2 ^ 59
def prefixEnd_1705242 : Nat := 4983230072969 + 3 ^ 40 * 1705242 * 2
def baseEnd_1705242 : Nat := 875608778234322466532741

theorem tailTrace_1705242 : CollatzResearch.WordTrace tailWord_1705242 prefixEnd_1705242 875608778234322466532741 := by
  unfold tailWord_1705242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15548821322051735248133495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41463523525471293995022653 15548821322051735248133495)
  ·
    refine ⟨23323231983077602872200243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15548821322051735248133495 23323231983077602872200243)
    ·
      refine ⟨34984847974616404308300365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23323231983077602872200243 34984847974616404308300365)
      ·
        refine ⟨13119317990481151615612637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34984847974616404308300365 13119317990481151615612637)
        ·
          refine ⟨4919744246430431855854739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13119317990481151615612637 4919744246430431855854739)
          ·
            refine ⟨7379616369645647783782109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919744246430431855854739 7379616369645647783782109)
            ·
              refine ⟨2767356138617117918918291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7379616369645647783782109 2767356138617117918918291)
              ·
                refine ⟨4151034207925676878377437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767356138617117918918291 4151034207925676878377437)
                ·
                  refine ⟨1556637827972128829391539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4151034207925676878377437 1556637827972128829391539)
                  ·
                    refine ⟨2334956741958193244087309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556637827972128829391539 2334956741958193244087309)
                    ·
                      refine ⟨875608778234322466532741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2334956741958193244087309 875608778234322466532741)
                      ·
                        rfl

theorem cell23_1705242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_1705242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705242 prefixEnd_1705242 := by exact prefixLift 1705242
  have htrace : WordTrace (prefixWord ++ tailWord_1705242) baseStart_1705242 baseEnd_1705242 := by
    simpa [prefixWord, tailWord_1705242, baseEnd_1705242] using wordTrace_append hprefix tailTrace_1705242
  have hstable : (prefixWord ++ tailWord_1705242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705242).length < 2 ^ (prefixWord ++ tailWord_1705242).sum := by decide
  have hdescent : baseEnd_1705242 < baseStart_1705242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705265 : List Nat := [1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 4]
def baseStart_1705265 : Nat := 118140960795 + 1705265 * 2 ^ 59
def prefixEnd_1705265 : Nat := 4983230072969 + 3 ^ 40 * 1705265 * 2
def baseEnd_1705265 : Nat := 875620588289375876545135

theorem tailTrace_1705265 : CollatzResearch.WordTrace tailWord_1705265 prefixEnd_1705265 875620588289375876545135 := by
  unfold tailWord_1705265
  simp only [CollatzResearch.WordTrace]
  refine ⟨62196124167123615920621249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41464082778082410613747499 62196124167123615920621249)
  ·
    refine ⟨46647093125342711940465937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62196124167123615920621249 46647093125342711940465937)
    ·
      refine ⟨34985319844007033955349453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46647093125342711940465937 34985319844007033955349453)
      ·
        refine ⟨13119494941502637733256045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34985319844007033955349453 13119494941502637733256045)
        ·
          refine ⟨4919810603063489149971017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13119494941502637733256045 4919810603063489149971017)
          ·
            refine ⟨3689857952297616862478263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4919810603063489149971017 3689857952297616862478263)
            ·
              refine ⟨5534786928446425293717395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689857952297616862478263 5534786928446425293717395)
              ·
                refine ⟨8302180392669637940576093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5534786928446425293717395 8302180392669637940576093)
                ·
                  refine ⟨3113317647251114227716035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8302180392669637940576093 3113317647251114227716035)
                  ·
                    refine ⟨4669976470876671341574053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3113317647251114227716035 4669976470876671341574053)
                    ·
                      refine ⟨875620588289375876545135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4669976470876671341574053 875620588289375876545135)
                      ·
                        rfl

theorem cell23_1705265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_1705265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705265 prefixEnd_1705265 := by exact prefixLift 1705265
  have htrace : WordTrace (prefixWord ++ tailWord_1705265) baseStart_1705265 baseEnd_1705265 := by
    simpa [prefixWord, tailWord_1705265, baseEnd_1705265] using wordTrace_append hprefix tailTrace_1705265
  have hstable : (prefixWord ++ tailWord_1705265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705265).length < 2 ^ (prefixWord ++ tailWord_1705265).sum := by decide
  have hdescent : baseEnd_1705265 < baseStart_1705265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705285 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_1705285 : Nat := 118140960795 + 1705285 * 2 ^ 59
def prefixEnd_1705285 : Nat := 4983230072969 + 3 ^ 40 * 1705285 * 2
def baseEnd_1705285 : Nat := 875630857902465798295043

theorem tailTrace_1705285 : CollatzResearch.WordTrace tailWord_1705285 prefixEnd_1705285 875630857902465798295043 := by
  unfold tailWord_1705285
  simp only [CollatzResearch.WordTrace]
  refine ⟨62196853627051159336349309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41464569084700772890899539 62196853627051159336349309)
  ·
    refine ⟨23323820110144184751130991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62196853627051159336349309 23323820110144184751130991)
    ·
      refine ⟨34985730165216277126696487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23323820110144184751130991 34985730165216277126696487)
      ·
        refine ⟨52478595247824415690044731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34985730165216277126696487 52478595247824415690044731)
        ·
          refine ⟨78717892871736623535067097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52478595247824415690044731 78717892871736623535067097)
          ·
            refine ⟨59038419653802467651300323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78717892871736623535067097 59038419653802467651300323)
            ·
              refine ⟨88557629480703701476950485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59038419653802467651300323 88557629480703701476950485)
              ·
                refine ⟨2075569440953993003366027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88557629480703701476950485 2075569440953993003366027)
                ·
                  refine ⟨3113354161430989505049041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075569440953993003366027 3113354161430989505049041)
                  ·
                    refine ⟨2335015621073242128786781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3113354161430989505049041 2335015621073242128786781)
                    ·
                      refine ⟨875630857902465798295043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335015621073242128786781 875630857902465798295043)
                      ·
                        rfl

theorem cell23_1705285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_1705285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705285 prefixEnd_1705285 := by exact prefixLift 1705285
  have htrace : WordTrace (prefixWord ++ tailWord_1705285) baseStart_1705285 baseEnd_1705285 := by
    simpa [prefixWord, tailWord_1705285, baseEnd_1705285] using wordTrace_append hprefix tailTrace_1705285
  have hstable : (prefixWord ++ tailWord_1705285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705285).length < 2 ^ (prefixWord ++ tailWord_1705285).sum := by decide
  have hdescent : baseEnd_1705285 < baseStart_1705285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705292 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_1705292 : Nat := 118140960795 + 1705292 * 2 ^ 59
def prefixEnd_1705292 : Nat := 4983230072969 + 3 ^ 40 * 1705292 * 2
def baseEnd_1705292 : Nat := 291878150755682423635837

theorem tailTrace_1705292 : CollatzResearch.WordTrace tailWord_1705292 prefixEnd_1705292 291878150755682423635837 := by
  unfold tailWord_1705292
  simp only [CollatzResearch.WordTrace]
  refine ⟨31098554469012899765927065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41464739292017199687902753 31098554469012899765927065)
  ·
    refine ⟨23323915851759674824445299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31098554469012899765927065 23323915851759674824445299)
    ·
      refine ⟨34985873777639512236667949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23323915851759674824445299 34985873777639512236667949)
      ·
        refine ⟨13119702666614817088750481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34985873777639512236667949 13119702666614817088750481)
        ·
          refine ⟨9839776999961112816562861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13119702666614817088750481 9839776999961112816562861)
          ·
            refine ⟨3689916374985417306211073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9839776999961112816562861 3689916374985417306211073)
            ·
              refine ⟨2767437281239062979658305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3689916374985417306211073 2767437281239062979658305)
              ·
                refine ⟨2075577960929297234743729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767437281239062979658305 2075577960929297234743729)
                ·
                  refine ⟨1556683470696972926057797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075577960929297234743729 1556683470696972926057797)
                  ·
                    refine ⟨291878150755682423635837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1556683470696972926057797 291878150755682423635837)
                    ·
                      rfl

theorem cell23_1705292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_1705292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705292 prefixEnd_1705292 := by exact prefixLift 1705292
  have htrace : WordTrace (prefixWord ++ tailWord_1705292) baseStart_1705292 baseEnd_1705292 := by
    simpa [prefixWord, tailWord_1705292, baseEnd_1705292] using wordTrace_append hprefix tailTrace_1705292
  have hstable : (prefixWord ++ tailWord_1705292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705292).length < 2 ^ (prefixWord ++ tailWord_1705292).sum := by decide
  have hdescent : baseEnd_1705292 < baseStart_1705292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705293 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1705293 : Nat := 118140960795 + 1705293 * 2 ^ 59
def prefixEnd_1705293 : Nat := 4983230072969 + 3 ^ 40 * 1705293 * 2
def baseEnd_1705293 : Nat := 875634965747701766995007

theorem tailTrace_1705293 : CollatzResearch.WordTrace tailWord_1705293 prefixEnd_1705293 875634965747701766995007 := by
  unfold tailWord_1705293
  simp only [CollatzResearch.WordTrace]
  refine ⟨62197145411022176702640533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41464763607348117801760355 62197145411022176702640533)
  ·
    refine ⟨2915491191141664532936275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62197145411022176702640533 2915491191141664532936275)
    ·
      refine ⟨4373236786712496799404413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915491191141664532936275 4373236786712496799404413)
      ·
        refine ⟨1639963795017186299776655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4373236786712496799404413 1639963795017186299776655)
        ·
          refine ⟨2459945692525779449664983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639963795017186299776655 2459945692525779449664983)
          ·
            refine ⟨3689918538788669174497475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459945692525779449664983 3689918538788669174497475)
            ·
              refine ⟨5534877808183003761746213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689918538788669174497475 5534877808183003761746213)
              ·
                refine ⟨1037789589034313205327415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5534877808183003761746213 1037789589034313205327415)
                ·
                  refine ⟨1556684383551469807991123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037789589034313205327415 1556684383551469807991123)
                  ·
                    refine ⟨2335026575327204711986685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556684383551469807991123 2335026575327204711986685)
                    ·
                      refine ⟨875634965747701766995007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335026575327204711986685 875634965747701766995007)
                      ·
                        rfl

theorem cell23_1705293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1705293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705293 prefixEnd_1705293 := by exact prefixLift 1705293
  have htrace : WordTrace (prefixWord ++ tailWord_1705293) baseStart_1705293 baseEnd_1705293 := by
    simpa [prefixWord, tailWord_1705293, baseEnd_1705293] using wordTrace_append hprefix tailTrace_1705293
  have hstable : (prefixWord ++ tailWord_1705293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705293).length < 2 ^ (prefixWord ++ tailWord_1705293).sum := by decide
  have hdescent : baseEnd_1705293 < baseStart_1705293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705299 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 1, 2, 2]
def baseStart_1705299 : Nat := 118140960795 + 1705299 * 2 ^ 59
def prefixEnd_1705299 : Nat := 4983230072969 + 3 ^ 40 * 1705299 * 2
def baseEnd_1705299 : Nat := 875638046631628743519979

theorem tailTrace_1705299 : CollatzResearch.WordTrace tailWord_1705299 prefixEnd_1705299 875638046631628743519979 := by
  unfold tailWord_1705299
  simp only [CollatzResearch.WordTrace]
  refine ⟨62197364249000439727358951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41464909499333626484905967 62197364249000439727358951)
  ·
    refine ⟨93296046373500659591038427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62197364249000439727358951 93296046373500659591038427)
    ·
      refine ⟨139944069560250989386557641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93296046373500659591038427 139944069560250989386557641)
      ·
        refine ⟨104958052170188242039918231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139944069560250989386557641 104958052170188242039918231)
        ·
          refine ⟨157437078255282363059877347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104958052170188242039918231 157437078255282363059877347)
          ·
            refine ⟨236155617382923544589816021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157437078255282363059877347 236155617382923544589816021)
            ·
              refine ⟨5534897282412270576323813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 236155617382923544589816021 5534897282412270576323813)
              ·
                refine ⟨1037793240452300733060715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5534897282412270576323813 1037793240452300733060715)
                ·
                  refine ⟨1556689860678451099591073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037793240452300733060715 1556689860678451099591073)
                  ·
                    refine ⟨1167517395508838324693305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1556689860678451099591073 1167517395508838324693305)
                    ·
                      refine ⟨875638046631628743519979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167517395508838324693305 875638046631628743519979)
                      ·
                        rfl

theorem cell23_1705299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 1, 2, 2].length) (baseStart_1705299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705299 prefixEnd_1705299 := by exact prefixLift 1705299
  have htrace : WordTrace (prefixWord ++ tailWord_1705299) baseStart_1705299 baseEnd_1705299 := by
    simpa [prefixWord, tailWord_1705299, baseEnd_1705299] using wordTrace_append hprefix tailTrace_1705299
  have hstable : (prefixWord ++ tailWord_1705299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705299).length < 2 ^ (prefixWord ++ tailWord_1705299).sum := by decide
  have hdescent : baseEnd_1705299 < baseStart_1705299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705315 : List Nat := [1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1705315 : Nat := 118140960795 + 1705315 * 2 ^ 59
def prefixEnd_1705315 : Nat := 4983230072969 + 3 ^ 40 * 1705315 * 2
def baseEnd_1705315 : Nat := 875646262322100680919905

theorem tailTrace_1705315 : CollatzResearch.WordTrace tailWord_1705315 prefixEnd_1705315 875646262322100680919905 := by
  unfold tailWord_1705315
  simp only [CollatzResearch.WordTrace]
  refine ⟨62197947816942474459941399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41465298544628316306627599 62197947816942474459941399)
  ·
    refine ⟨93296921725413711689912099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62197947816942474459941399 93296921725413711689912099)
    ·
      refine ⟨139945382588120567534868149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93296921725413711689912099 139945382588120567534868149)
      ·
        refine ⟨13119879617636303206393889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139945382588120567534868149 13119879617636303206393889)
        ·
          refine ⟨9839909713227227404795417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13119879617636303206393889 9839909713227227404795417)
          ·
            refine ⟨7379932284920420553596563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9839909713227227404795417 7379932284920420553596563)
            ·
              refine ⟨11069898427380630830394845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379932284920420553596563 11069898427380630830394845)
              ·
                refine ⟨4151211910267736561398067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11069898427380630830394845 4151211910267736561398067)
                ·
                  refine ⟨6226817865401604842097101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151211910267736561398067 6226817865401604842097101)
                  ·
                    refine ⟨2335056699525601815786413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6226817865401604842097101 2335056699525601815786413)
                    ·
                      refine ⟨875646262322100680919905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335056699525601815786413 875646262322100680919905)
                      ·
                        rfl

theorem cell23_1705315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1705315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705315 prefixEnd_1705315 := by exact prefixLift 1705315
  have htrace : WordTrace (prefixWord ++ tailWord_1705315) baseStart_1705315 baseEnd_1705315 := by
    simpa [prefixWord, tailWord_1705315, baseEnd_1705315] using wordTrace_append hprefix tailTrace_1705315
  have hstable : (prefixWord ++ tailWord_1705315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705315).length < 2 ^ (prefixWord ++ tailWord_1705315).sum := by decide
  have hdescent : baseEnd_1705315 < baseStart_1705315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705322 : List Nat := [3, 1, 3, 3, 2, 1, 3, 7]
def baseStart_1705322 : Nat := 118140960795 + 1705322 * 2 ^ 59
def prefixEnd_1705322 : Nat := 4983230072969 + 3 ^ 40 * 1705322 * 2
def baseEnd_1705322 : Nat := 32431476173580820501199

theorem tailTrace_1705322 : CollatzResearch.WordTrace tailWord_1705322 prefixEnd_1705322 32431476173580820501199 := by
  unfold tailWord_1705322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549550781979278663861555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41465468751944743103630813 15549550781979278663861555)
  ·
    refine ⟨23324326172968917995792333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15549550781979278663861555 23324326172968917995792333)
    ·
      refine ⟨8746622314863344248422125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23324326172968917995792333 8746622314863344248422125)
      ·
        refine ⟨3279983368073754093158297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8746622314863344248422125 3279983368073754093158297)
        ·
          refine ⟨2459987526055315569868723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3279983368073754093158297 2459987526055315569868723)
          ·
            refine ⟨3689981289082973354803085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459987526055315569868723 3689981289082973354803085)
            ·
              refine ⟨1383742983406115008051157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3689981289082973354803085 1383742983406115008051157)
              ·
                refine ⟨32431476173580820501199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1383742983406115008051157 32431476173580820501199)
                ·
                  rfl

theorem cell23_1705322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 3, 7].length) (baseStart_1705322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705322 prefixEnd_1705322 := by exact prefixLift 1705322
  have htrace : WordTrace (prefixWord ++ tailWord_1705322) baseStart_1705322 baseEnd_1705322 := by
    simpa [prefixWord, tailWord_1705322, baseEnd_1705322] using wordTrace_append hprefix tailTrace_1705322
  have hstable : (prefixWord ++ tailWord_1705322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705322).length < 2 ^ (prefixWord ++ tailWord_1705322).sum := by decide
  have hdescent : baseEnd_1705322 < baseStart_1705322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705328 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_1705328 : Nat := 118140960795 + 1705328 * 2 ^ 59
def prefixEnd_1705328 : Nat := 4983230072969 + 3 ^ 40 * 1705328 * 2
def baseEnd_1705328 : Nat := 875652937570609130057345

theorem tailTrace_1705328 : CollatzResearch.WordTrace tailWord_1705328 prefixEnd_1705328 875652937570609130057345 := by
  unfold tailWord_1705328
  simp only [CollatzResearch.WordTrace]
  refine ⟨31099210982947688840082319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41465614643930251786776425 31099210982947688840082319)
  ·
    refine ⟨46648816474421533260123479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31099210982947688840082319 46648816474421533260123479)
    ·
      refine ⟨69973224711632299890185219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46648816474421533260123479 69973224711632299890185219)
      ·
        refine ⟨104959837067448449835277829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69973224711632299890185219 104959837067448449835277829)
        ·
          refine ⟨19679969450146584344114593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104959837067448449835277829 19679969450146584344114593)
          ·
            refine ⟨14759977087609938258085945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19679969450146584344114593 14759977087609938258085945)
            ·
              refine ⟨11069982815707453693564459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14759977087609938258085945 11069982815707453693564459)
              ·
                refine ⟨16604974223561180540346689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11069982815707453693564459 16604974223561180540346689)
                ·
                  refine ⟨12453730667670885405260017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16604974223561180540346689 12453730667670885405260017)
                  ·
                    refine ⟨9340298000753164053945013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12453730667670885405260017 9340298000753164053945013)
                    ·
                      refine ⟨875652937570609130057345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9340298000753164053945013 875652937570609130057345)
                      ·
                        rfl

theorem cell23_1705328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_1705328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705328 prefixEnd_1705328 := by exact prefixLift 1705328
  have htrace : WordTrace (prefixWord ++ tailWord_1705328) baseStart_1705328 baseEnd_1705328 := by
    simpa [prefixWord, tailWord_1705328, baseEnd_1705328] using wordTrace_append hprefix tailTrace_1705328
  have hstable : (prefixWord ++ tailWord_1705328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705328).length < 2 ^ (prefixWord ++ tailWord_1705328).sum := by decide
  have hdescent : baseEnd_1705328 < baseStart_1705328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705333 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_1705333 : Nat := 118140960795 + 1705333 * 2 ^ 59
def prefixEnd_1705333 : Nat := 4983230072969 + 3 ^ 40 * 1705333 * 2
def baseEnd_1705333 : Nat := 875655504973881610494823

theorem tailTrace_1705333 : CollatzResearch.WordTrace tailWord_1705333 prefixEnd_1705333 875655504973881610494823 := by
  unfold tailWord_1705333
  simp only [CollatzResearch.WordTrace]
  refine ⟨62198604330877263534096653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41465736220584842356064435 62198604330877263534096653)
  ·
    refine ⟨23324476624078973825286245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62198604330877263534096653 23324476624078973825286245)
    ·
      refine ⟨4373339367014807592241171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23324476624078973825286245 4373339367014807592241171)
      ·
        refine ⟨6560009050522211388361757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373339367014807592241171 6560009050522211388361757)
        ·
          refine ⟨2460003393945829270635659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6560009050522211388361757 2460003393945829270635659)
          ·
            refine ⟨3690005090918743905953489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460003393945829270635659 3690005090918743905953489)
            ·
              refine ⟨2767503818189057929465117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690005090918743905953489 2767503818189057929465117)
              ·
                refine ⟨1037813931820896723549419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2767503818189057929465117 1037813931820896723549419)
                ·
                  refine ⟨1556720897731345085324129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037813931820896723549419 1556720897731345085324129)
                  ·
                    refine ⟨1167540673298508813993097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1556720897731345085324129 1167540673298508813993097)
                    ·
                      refine ⟨875655504973881610494823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167540673298508813993097 875655504973881610494823)
                      ·
                        rfl

theorem cell23_1705333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_1705333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705333 prefixEnd_1705333 := by exact prefixLift 1705333
  have htrace : WordTrace (prefixWord ++ tailWord_1705333) baseStart_1705333 baseEnd_1705333 := by
    simpa [prefixWord, tailWord_1705333, baseEnd_1705333] using wordTrace_append hprefix tailTrace_1705333
  have hstable : (prefixWord ++ tailWord_1705333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705333).length < 2 ^ (prefixWord ++ tailWord_1705333).sum := by decide
  have hdescent : baseEnd_1705333 < baseStart_1705333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705338 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_1705338 : Nat := 118140960795 + 1705338 * 2 ^ 59
def prefixEnd_1705338 : Nat := 4983230072969 + 3 ^ 40 * 1705338 * 2
def baseEnd_1705338 : Nat := 875658072377154090932299

theorem tailTrace_1705338 : CollatzResearch.WordTrace tailWord_1705338 prefixEnd_1705338 875658072377154090932299 := by
  unfold tailWord_1705338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15549696673964787347007167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41465857797239432925352445 15549696673964787347007167)
  ·
    refine ⟨23324545010947181020510751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15549696673964787347007167 23324545010947181020510751)
    ·
      refine ⟨34986817516420771530766127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23324545010947181020510751 34986817516420771530766127)
      ·
        refine ⟨52480226274631157296149191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34986817516420771530766127 52480226274631157296149191)
        ·
          refine ⟨78720339411946735944223787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52480226274631157296149191 78720339411946735944223787)
          ·
            refine ⟨118080509117920103916335681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78720339411946735944223787 118080509117920103916335681)
            ·
              refine ⟨88560381838440077937251761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118080509117920103916335681 88560381838440077937251761)
              ·
                refine ⟨66420286378830058452938821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88560381838440077937251761 66420286378830058452938821)
                ·
                  refine ⟨12453803696030635959926029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66420286378830058452938821 12453803696030635959926029)
                  ·
                    refine ⟨4670176386011488484972261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12453803696030635959926029 4670176386011488484972261)
                    ·
                      refine ⟨875658072377154090932299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4670176386011488484972261 875658072377154090932299)
                      ·
                        rfl

theorem cell23_1705338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_1705338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705338 prefixEnd_1705338 := by exact prefixLift 1705338
  have htrace : WordTrace (prefixWord ++ tailWord_1705338) baseStart_1705338 baseEnd_1705338 := by
    simpa [prefixWord, tailWord_1705338, baseEnd_1705338] using wordTrace_append hprefix tailTrace_1705338
  have hstable : (prefixWord ++ tailWord_1705338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705338).length < 2 ^ (prefixWord ++ tailWord_1705338).sum := by decide
  have hdescent : baseEnd_1705338 < baseStart_1705338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705412 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 7]
def baseStart_1705412 : Nat := 118140960795 + 1705412 * 2 ^ 59
def prefixEnd_1705412 : Nat := 4983230072969 + 3 ^ 40 * 1705412 * 2
def baseEnd_1705412 : Nat := 97299563327287422378551

theorem tailTrace_1705412 : CollatzResearch.WordTrace tailWord_1705412 prefixEnd_1705412 97299563327287422378551 := by
  unfold tailWord_1705412
  simp only [CollatzResearch.WordTrace]
  refine ⟨31100742848795530013111245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41467657131727373350814993 31100742848795530013111245)
  ·
    refine ⟨11662778568298323754916717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31100742848795530013111245 11662778568298323754916717)
    ·
      refine ⟨4373541963111871408093769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11662778568298323754916717 4373541963111871408093769)
      ·
        refine ⟨3280156472333903556070327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4373541963111871408093769 3280156472333903556070327)
        ·
          refine ⟨4920234708500855334105491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280156472333903556070327 4920234708500855334105491)
          ·
            refine ⟨7380352062751283001158237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920234708500855334105491 7380352062751283001158237)
            ·
              refine ⟨2767632023531731125434339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7380352062751283001158237 2767632023531731125434339)
              ·
                refine ⟨4151448035297596688151509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767632023531731125434339 4151448035297596688151509)
                ·
                  refine ⟨97299563327287422378551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4151448035297596688151509 97299563327287422378551)
                  ·
                    rfl

theorem cell23_1705412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_1705412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705412 prefixEnd_1705412 := by exact prefixLift 1705412
  have htrace : WordTrace (prefixWord ++ tailWord_1705412) baseStart_1705412 baseEnd_1705412 := by
    simpa [prefixWord, tailWord_1705412, baseEnd_1705412] using wordTrace_append hprefix tailTrace_1705412
  have hstable : (prefixWord ++ tailWord_1705412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705412).length < 2 ^ (prefixWord ++ tailWord_1705412).sum := by decide
  have hdescent : baseEnd_1705412 < baseStart_1705412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705465 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1705465 : Nat := 118140960795 + 1705465 * 2 ^ 59
def prefixEnd_1705465 : Nat := 4983230072969 + 3 ^ 40 * 1705465 * 2
def baseEnd_1705465 : Nat := 875723284420275094044215

theorem tailTrace_1705465 : CollatzResearch.WordTrace tailWord_1705465 prefixEnd_1705465 875723284420275094044215 := by
  unfold tailWord_1705465
  simp only [CollatzResearch.WordTrace]
  refine ⟨62203418766399050077901849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41468945844266033385267899 62203418766399050077901849)
  ·
    refine ⟨46652564074799287558426387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62203418766399050077901849 46652564074799287558426387)
    ·
      refine ⟨69978846112198931337639581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46652564074799287558426387 69978846112198931337639581)
      ·
        refine ⟨26242067292074599251614843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69978846112198931337639581 26242067292074599251614843)
        ·
          refine ⟨39363100938111898877422265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26242067292074599251614843 39363100938111898877422265)
          ·
            refine ⟨29522325703583924158066699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39363100938111898877422265 29522325703583924158066699)
            ·
              refine ⟨44283488555375886237100049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29522325703583924158066699 44283488555375886237100049)
              ·
                refine ⟨33212616416531914677825037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44283488555375886237100049 33212616416531914677825037)
                ·
                  refine ⟨12454731156199468004184389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33212616416531914677825037 12454731156199468004184389)
                  ·
                    refine ⟨2335262091787400250784573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12454731156199468004184389 2335262091787400250784573)
                    ·
                      refine ⟨875723284420275094044215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335262091787400250784573 875723284420275094044215)
                      ·
                        rfl

theorem cell23_1705465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1705465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705465 prefixEnd_1705465 := by exact prefixLift 1705465
  have htrace : WordTrace (prefixWord ++ tailWord_1705465) baseStart_1705465 baseEnd_1705465 := by
    simpa [prefixWord, tailWord_1705465, baseEnd_1705465] using wordTrace_append hprefix tailTrace_1705465
  have hstable : (prefixWord ++ tailWord_1705465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705465).length < 2 ^ (prefixWord ++ tailWord_1705465).sum := by decide
  have hdescent : baseEnd_1705465 < baseStart_1705465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705479 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1705479 : Nat := 118140960795 + 1705479 * 2 ^ 59
def prefixEnd_1705479 : Nat := 4983230072969 + 3 ^ 40 * 1705479 * 2
def baseEnd_1705479 : Nat := 875730473149438039269151

theorem tailTrace_1705479 : CollatzResearch.WordTrace tailWord_1705479 prefixEnd_1705479 875730473149438039269151 := by
  unfold tailWord_1705479
  simp only [CollatzResearch.WordTrace]
  refine ⟨62203929388348330468911491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41469286258898886979274327 62203929388348330468911491)
  ·
    refine ⟨93305894082522495703367237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62203929388348330468911491 93305894082522495703367237)
    ·
      refine ⟨17494855140472967944381357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93305894082522495703367237 17494855140472967944381357)
      ·
        refine ⟨6560570677677362979143009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17494855140472967944381357 6560570677677362979143009)
        ·
          refine ⟨4920428008258022234357257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6560570677677362979143009 4920428008258022234357257)
          ·
            refine ⟨3690321006193516675767943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4920428008258022234357257 3690321006193516675767943)
            ·
              refine ⟨5535481509290275013651915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690321006193516675767943 5535481509290275013651915)
              ·
                refine ⟨8303222263935412520477873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535481509290275013651915 8303222263935412520477873)
                ·
                  refine ⟨6227416697951559390358405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8303222263935412520477873 6227416697951559390358405)
                  ·
                    refine ⟨1167640630865917385692201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6227416697951559390358405 1167640630865917385692201)
                    ·
                      refine ⟨875730473149438039269151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167640630865917385692201 875730473149438039269151)
                      ·
                        rfl

theorem cell23_1705479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1705479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705479 prefixEnd_1705479 := by exact prefixLift 1705479
  have htrace : WordTrace (prefixWord ++ tailWord_1705479) baseStart_1705479 baseEnd_1705479 := by
    simpa [prefixWord, tailWord_1705479, baseEnd_1705479] using wordTrace_append hprefix tailTrace_1705479
  have hstable : (prefixWord ++ tailWord_1705479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705479).length < 2 ^ (prefixWord ++ tailWord_1705479).sum := by decide
  have hdescent : baseEnd_1705479 < baseStart_1705479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705496 : List Nat := [2, 1, 2, 3, 5, 1, 1, 1, 2, 1, 4]
def baseStart_1705496 : Nat := 118140960795 + 1705496 * 2 ^ 59
def prefixEnd_1705496 : Nat := 4983230072969 + 3 ^ 40 * 1705496 * 2
def baseEnd_1705496 : Nat := 875739202320564472756573

theorem tailTrace_1705496 : CollatzResearch.WordTrace tailWord_1705496 prefixEnd_1705496 875739202320564472756573 := by
  unfold tailWord_1705496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31102274714643371186140171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41469699619524494914853561 31102274714643371186140171)
  ·
    refine ⟨46653412071965056779210257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31102274714643371186140171 46653412071965056779210257)
    ·
      refine ⟨34990059053973792584407693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46653412071965056779210257 34990059053973792584407693)
      ·
        refine ⟨13121272145240172219152885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34990059053973792584407693 13121272145240172219152885)
        ·
          refine ⟨1230119263616266145545583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13121272145240172219152885 1230119263616266145545583)
          ·
            refine ⟨1845178895424399218318375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230119263616266145545583 1845178895424399218318375)
            ·
              refine ⟨2767768343136598827477563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845178895424399218318375 2767768343136598827477563)
              ·
                refine ⟨4151652514704898241216345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767768343136598827477563 4151652514704898241216345)
                ·
                  refine ⟨3113739386028673680912259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4151652514704898241216345 3113739386028673680912259)
                  ·
                    refine ⟨4670609079043010521368389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3113739386028673680912259 4670609079043010521368389)
                    ·
                      refine ⟨875739202320564472756573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4670609079043010521368389 875739202320564472756573)
                      ·
                        rfl

theorem cell23_1705496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_1705496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705496 prefixEnd_1705496 := by exact prefixLift 1705496
  have htrace : WordTrace (prefixWord ++ tailWord_1705496) baseStart_1705496 baseEnd_1705496 := by
    simpa [prefixWord, tailWord_1705496, baseEnd_1705496] using wordTrace_append hprefix tailTrace_1705496
  have hstable : (prefixWord ++ tailWord_1705496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705496).length < 2 ^ (prefixWord ++ tailWord_1705496).sum := by decide
  have hdescent : baseEnd_1705496 < baseStart_1705496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705529 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1705529 : Nat := 118140960795 + 1705529 * 2 ^ 59
def prefixEnd_1705529 : Nat := 4983230072969 + 3 ^ 40 * 1705529 * 2
def baseEnd_1705529 : Nat := 875756147182162843643921

theorem tailTrace_1705529 : CollatzResearch.WordTrace tailWord_1705529 prefixEnd_1705529 875756147182162843643921 := by
  unfold tailWord_1705529
  simp only [CollatzResearch.WordTrace]
  refine ⟨62205753038167189008231641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41470502025444792672154427 62205753038167189008231641)
  ·
    refine ⟨46654314778625391756173731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62205753038167189008231641 46654314778625391756173731)
    ·
      refine ⟨69981472167938087634260597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46654314778625391756173731 69981472167938087634260597)
      ·
        refine ⟨6560763015744195715711931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69981472167938087634260597 6560763015744195715711931)
        ·
          refine ⟨9841144523616293573567897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560763015744195715711931 9841144523616293573567897)
          ·
            refine ⟨7380858392712220180175923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9841144523616293573567897 7380858392712220180175923)
            ·
              refine ⟨11071287589068330270263885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380858392712220180175923 11071287589068330270263885)
              ·
                refine ⟨4151732845900623851348957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11071287589068330270263885 4151732845900623851348957)
                ·
                  refine ⟨1556899817212733944255859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4151732845900623851348957 1556899817212733944255859)
                  ·
                    refine ⟨2335349725819100916383789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556899817212733944255859 2335349725819100916383789)
                    ·
                      refine ⟨875756147182162843643921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335349725819100916383789 875756147182162843643921)
                      ·
                        rfl

theorem cell23_1705529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1705529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705529 prefixEnd_1705529 := by exact prefixLift 1705529
  have htrace : WordTrace (prefixWord ++ tailWord_1705529) baseStart_1705529 baseEnd_1705529 := by
    simpa [prefixWord, tailWord_1705529, baseEnd_1705529] using wordTrace_append hprefix tailTrace_1705529
  have hstable : (prefixWord ++ tailWord_1705529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705529).length < 2 ^ (prefixWord ++ tailWord_1705529).sum := by decide
  have hdescent : baseEnd_1705529 < baseStart_1705529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705552 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 6, 2]
def baseStart_1705552 : Nat := 118140960795 + 1705552 * 2 ^ 59
def prefixEnd_1705552 : Nat := 4983230072969 + 3 ^ 40 * 1705552 * 2
def baseEnd_1705552 : Nat := 875767957237216253656315

theorem tailTrace_1705552 : CollatzResearch.WordTrace tailWord_1705552 prefixEnd_1705552 875767957237216253656315 := by
  unfold tailWord_1705552
  simp only [CollatzResearch.WordTrace]
  refine ⟨31103295958541931968159455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41471061278055909290879273 31103295958541931968159455)
  ·
    refine ⟨46654943937812897952239183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31103295958541931968159455 46654943937812897952239183)
    ·
      refine ⟨69982415906719346928358775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46654943937812897952239183 69982415906719346928358775)
      ·
        refine ⟨104973623860079020392538163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69982415906719346928358775 104973623860079020392538163)
        ·
          refine ⟨157460435790118530588807245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104973623860079020392538163 157460435790118530588807245)
          ·
            refine ⟨59047663421294448970802717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157460435790118530588807245 59047663421294448970802717)
            ·
              refine ⟨22142873782985418364051019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59047663421294448970802717 22142873782985418364051019)
              ·
                refine ⟨33214310674478127546076529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22142873782985418364051019 33214310674478127546076529)
                ·
                  refine ⟨24910733005858595659557397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33214310674478127546076529 24910733005858595659557397)
                  ·
                    refine ⟨1167690609649621671541753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24910733005858595659557397 1167690609649621671541753)
                    ·
                      refine ⟨875767957237216253656315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167690609649621671541753 875767957237216253656315)
                      ·
                        rfl

theorem cell23_1705552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 6, 2].length) (baseStart_1705552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705552 prefixEnd_1705552 := by exact prefixLift 1705552
  have htrace : WordTrace (prefixWord ++ tailWord_1705552) baseStart_1705552 baseEnd_1705552 := by
    simpa [prefixWord, tailWord_1705552, baseEnd_1705552] using wordTrace_append hprefix tailTrace_1705552
  have hstable : (prefixWord ++ tailWord_1705552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705552).length < 2 ^ (prefixWord ++ tailWord_1705552).sum := by decide
  have hdescent : baseEnd_1705552 < baseStart_1705552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705572 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_1705572 : Nat := 118140960795 + 1705572 * 2 ^ 59
def prefixEnd_1705572 : Nat := 4983230072969 + 3 ^ 40 * 1705572 * 2
def baseEnd_1705572 : Nat := 875778226850306175406223

theorem tailTrace_1705572 : CollatzResearch.WordTrace tailWord_1705572 prefixEnd_1705572 875778226850306175406223 := by
  unfold tailWord_1705572
  simp only [CollatzResearch.WordTrace]
  refine ⟨31103660688505703676023485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41471547584674271568031313 31103660688505703676023485)
  ·
    refine ⟨11663872758189638878508807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31103660688505703676023485 11663872758189638878508807)
    ·
      refine ⟨17495809137284458317763211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11663872758189638878508807 17495809137284458317763211)
      ·
        refine ⟨26243713705926687476644817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17495809137284458317763211 26243713705926687476644817)
        ·
          refine ⟨19682785279445015607483613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26243713705926687476644817 19682785279445015607483613)
          ·
            refine ⟨7381044479791880852806355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19682785279445015607483613 7381044479791880852806355)
            ·
              refine ⟨11071566719687821279209533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381044479791880852806355 11071566719687821279209533)
              ·
                refine ⟨4151837519882932979703575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11071566719687821279209533 4151837519882932979703575)
                ·
                  refine ⟨6227756279824399469555363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151837519882932979703575 6227756279824399469555363)
                  ·
                    refine ⟨9341634419736599204333045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6227756279824399469555363 9341634419736599204333045)
                    ·
                      refine ⟨875778226850306175406223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9341634419736599204333045 875778226850306175406223)
                      ·
                        rfl

theorem cell23_1705572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_1705572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705572 prefixEnd_1705572 := by exact prefixLift 1705572
  have htrace : WordTrace (prefixWord ++ tailWord_1705572) baseStart_1705572 baseEnd_1705572 := by
    simpa [prefixWord, tailWord_1705572, baseEnd_1705572] using wordTrace_append hprefix tailTrace_1705572
  have hstable : (prefixWord ++ tailWord_1705572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705572).length < 2 ^ (prefixWord ++ tailWord_1705572).sum := by decide
  have hdescent : baseEnd_1705572 < baseStart_1705572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705575 : List Nat := [1, 1, 5, 1, 1, 1, 13]
def baseStart_1705575 : Nat := 118140960795 + 1705575 * 2 ^ 59
def prefixEnd_1705575 : Nat := 4983230072969 + 3 ^ 40 * 1705575 * 2
def baseEnd_1705575 : Nat := 10812095892497156341589

theorem tailTrace_1705575 : CollatzResearch.WordTrace tailWord_1705575 prefixEnd_1705575 10812095892497156341589 := by
  unfold tailWord_1705575
  simp only [CollatzResearch.WordTrace]
  refine ⟨62207430796000538864406179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41471620530667025909604119 62207430796000538864406179)
  ·
    refine ⟨93311146194000808296609269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62207430796000538864406179 93311146194000808296609269)
    ·
      refine ⟨8747919955687575777807119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93311146194000808296609269 8747919955687575777807119)
      ·
        refine ⟨13121879933531363666710679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747919955687575777807119 13121879933531363666710679)
        ·
          refine ⟨19682819900297045500066019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13121879933531363666710679 19682819900297045500066019)
          ·
            refine ⟨29524229850445568250099029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19682819900297045500066019 29524229850445568250099029)
            ·
              refine ⟨10812095892497156341589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 29524229850445568250099029 10812095892497156341589)
              ·
                rfl

theorem cell23_1705575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 13].length) (baseStart_1705575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705575 prefixEnd_1705575 := by exact prefixLift 1705575
  have htrace : WordTrace (prefixWord ++ tailWord_1705575) baseStart_1705575 baseEnd_1705575 := by
    simpa [prefixWord, tailWord_1705575, baseEnd_1705575] using wordTrace_append hprefix tailTrace_1705575
  have hstable : (prefixWord ++ tailWord_1705575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705575).length < 2 ^ (prefixWord ++ tailWord_1705575).sum := by decide
  have hdescent : baseEnd_1705575 < baseStart_1705575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705589 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1705589 : Nat := 118140960795 + 1705589 * 2 ^ 59
def prefixEnd_1705589 : Nat := 4983230072969 + 3 ^ 40 * 1705589 * 2
def baseEnd_1705589 : Nat := 875786956021432608893645

theorem tailTrace_1705589 : CollatzResearch.WordTrace tailWord_1705589 prefixEnd_1705589 875786956021432608893645 := by
  unfold tailWord_1705589
  simp only [CollatzResearch.WordTrace]
  refine ⟨62207941417949819255415821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41471960945299879503610547 62207941417949819255415821)
  ·
    refine ⟨23327978031731182220780933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62207941417949819255415821 23327978031731182220780933)
    ·
      refine ⟨4373995880949596666396425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23327978031731182220780933 4373995880949596666396425)
      ·
        refine ⟨3280496910712197499797319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4373995880949596666396425 3280496910712197499797319)
        ·
          refine ⟨4920745366068296249695979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280496910712197499797319 4920745366068296249695979)
          ·
            refine ⟨7381118049102444374543969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920745366068296249695979 7381118049102444374543969)
            ·
              refine ⟨5535838536826833280907977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7381118049102444374543969 5535838536826833280907977)
              ·
                refine ⟨4151878902620124960680983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5535838536826833280907977 4151878902620124960680983)
                ·
                  refine ⟨6227818353930187441021475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151878902620124960680983 6227818353930187441021475)
                  ·
                    refine ⟨9341727530895281161532213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6227818353930187441021475 9341727530895281161532213)
                    ·
                      refine ⟨875786956021432608893645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9341727530895281161532213 875786956021432608893645)
                      ·
                        rfl

theorem cell23_1705589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1705589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705589 prefixEnd_1705589 := by exact prefixLift 1705589
  have htrace : WordTrace (prefixWord ++ tailWord_1705589) baseStart_1705589 baseEnd_1705589 := by
    simpa [prefixWord, tailWord_1705589, baseEnd_1705589] using wordTrace_append hprefix tailTrace_1705589
  have hstable : (prefixWord ++ tailWord_1705589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705589).length < 2 ^ (prefixWord ++ tailWord_1705589).sum := by decide
  have hdescent : baseEnd_1705589 < baseStart_1705589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705595 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_1705595 : Nat := 118140960795 + 1705595 * 2 ^ 59
def prefixEnd_1705595 : Nat := 4983230072969 + 3 ^ 40 * 1705595 * 2
def baseEnd_1705595 : Nat := 875790036905359585418617

theorem tailTrace_1705595 : CollatzResearch.WordTrace tailWord_1705595 prefixEnd_1705595 875790036905359585418617 := by
  unfold tailWord_1705595
  simp only [CollatzResearch.WordTrace]
  refine ⟨62208160255928082280134239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41472106837285388186756159 62208160255928082280134239)
  ·
    refine ⟨93312240383892123420201359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62208160255928082280134239 93312240383892123420201359)
    ·
      refine ⟨139968360575838185130302039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93312240383892123420201359 139968360575838185130302039)
      ·
        refine ⟨209952540863757277695453059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139968360575838185130302039 209952540863757277695453059)
        ·
          refine ⟨314928811295635916543179589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209952540863757277695453059 314928811295635916543179589)
          ·
            refine ⟨59049152117931734351846173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314928811295635916543179589 59049152117931734351846173)
            ·
              refine ⟨22143432044224400381942315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59049152117931734351846173 22143432044224400381942315)
              ·
                refine ⟨33215148066336600572913473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22143432044224400381942315 33215148066336600572913473)
                ·
                  refine ⟨24911361049752450429685105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33215148066336600572913473 24911361049752450429685105)
                  ·
                    refine ⟨18683520787314337822263829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24911361049752450429685105 18683520787314337822263829)
                    ·
                      refine ⟨875790036905359585418617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18683520787314337822263829 875790036905359585418617)
                      ·
                        rfl

theorem cell23_1705595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_1705595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705595 prefixEnd_1705595 := by exact prefixLift 1705595
  have htrace : WordTrace (prefixWord ++ tailWord_1705595) baseStart_1705595 baseEnd_1705595 := by
    simpa [prefixWord, tailWord_1705595, baseEnd_1705595] using wordTrace_append hprefix tailTrace_1705595
  have hstable : (prefixWord ++ tailWord_1705595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705595).length < 2 ^ (prefixWord ++ tailWord_1705595).sum := by decide
  have hdescent : baseEnd_1705595 < baseStart_1705595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705636 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_1705636 : Nat := 118140960795 + 1705636 * 2 ^ 59
def prefixEnd_1705636 : Nat := 4983230072969 + 3 ^ 40 * 1705636 * 2
def baseEnd_1705636 : Nat := 875811089612193925005929

theorem tailTrace_1705636 : CollatzResearch.WordTrace tailWord_1705636 prefixEnd_1705636 875811089612193925005929 := by
  unfold tailWord_1705636
  simp only [CollatzResearch.WordTrace]
  refine ⟨31104827824389773141188381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41473103765853030854917841 31104827824389773141188381)
  ·
    refine ⟨11664310434146164927945643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31104827824389773141188381 11664310434146164927945643)
    ·
      refine ⟨17496465651219247391918465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664310434146164927945643 17496465651219247391918465)
      ·
        refine ⟨13122349238414435543938849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17496465651219247391918465 13122349238414435543938849)
        ·
          refine ⟨9841761928810826657954137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13122349238414435543938849 9841761928810826657954137)
          ·
            refine ⟨7381321446608119993465603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9841761928810826657954137 7381321446608119993465603)
            ·
              refine ⟨11071982169912179990198405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381321446608119993465603 11071982169912179990198405)
              ·
                refine ⟨2075996656858533748162201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11071982169912179990198405 2075996656858533748162201)
                ·
                  refine ⟨1556997492643900311121651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2075996656858533748162201 1556997492643900311121651)
                  ·
                    refine ⟨2335496238965850466682477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1556997492643900311121651 2335496238965850466682477)
                    ·
                      refine ⟨875811089612193925005929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335496238965850466682477 875811089612193925005929)
                      ·
                        rfl

theorem cell23_1705636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_1705636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705636 prefixEnd_1705636 := by exact prefixLift 1705636
  have htrace : WordTrace (prefixWord ++ tailWord_1705636) baseStart_1705636 baseEnd_1705636 := by
    simpa [prefixWord, tailWord_1705636, baseEnd_1705636] using wordTrace_append hprefix tailTrace_1705636
  have hstable : (prefixWord ++ tailWord_1705636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705636).length < 2 ^ (prefixWord ++ tailWord_1705636).sum := by decide
  have hdescent : baseEnd_1705636 < baseStart_1705636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705672 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1705672 : Nat := 118140960795 + 1705672 * 2 ^ 59
def prefixEnd_1705672 : Nat := 4983230072969 + 3 ^ 40 * 1705672 * 2
def baseEnd_1705672 : Nat := 875829574915755784155763

theorem tailTrace_1705672 : CollatzResearch.WordTrace tailWord_1705672 prefixEnd_1705672 875829574915755784155763 := by
  unfold tailWord_1705672
  simp only [CollatzResearch.WordTrace]
  refine ⟨31105484338324562215343635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41473979117766082953791513 31105484338324562215343635)
  ·
    refine ⟨46658226507486843323015453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31105484338324562215343635 46658226507486843323015453)
    ·
      refine ⟨17496834940307566246130795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46658226507486843323015453 17496834940307566246130795)
      ·
        refine ⟨26245252410461349369196193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17496834940307566246130795 26245252410461349369196193)
        ·
          refine ⟨19683939307846012026897145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26245252410461349369196193 19683939307846012026897145)
          ·
            refine ⟨14762954480884509020172859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19683939307846012026897145 14762954480884509020172859)
            ·
              refine ⟨22144431721326763530259289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14762954480884509020172859 22144431721326763530259289)
              ·
                refine ⟨16608323790995072647694467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22144431721326763530259289 16608323790995072647694467)
                ·
                  refine ⟨24912485686492608971541701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16608323790995072647694467 24912485686492608971541701)
                  ·
                    refine ⟨4671091066217364182164069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24912485686492608971541701 4671091066217364182164069)
                    ·
                      refine ⟨875829574915755784155763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4671091066217364182164069 875829574915755784155763)
                      ·
                        rfl

theorem cell23_1705672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1705672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705672 prefixEnd_1705672 := by exact prefixLift 1705672
  have htrace : WordTrace (prefixWord ++ tailWord_1705672) baseStart_1705672 baseEnd_1705672 := by
    simpa [prefixWord, tailWord_1705672, baseEnd_1705672] using wordTrace_append hprefix tailTrace_1705672
  have hstable : (prefixWord ++ tailWord_1705672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705672).length < 2 ^ (prefixWord ++ tailWord_1705672).sum := by decide
  have hdescent : baseEnd_1705672 < baseStart_1705672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705710 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_1705710 : Nat := 118140960795 + 1705710 * 2 ^ 59
def prefixEnd_1705710 : Nat := 4983230072969 + 3 ^ 40 * 1705710 * 2
def baseEnd_1705710 : Nat := 875849087180626635480589

theorem tailTrace_1705710 : CollatzResearch.WordTrace tailWord_1705710 prefixEnd_1705710 875849087180626635480589 := by
  unfold tailWord_1705710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776544331313932115071323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41474903100340971280380389 7776544331313932115071323)
  ·
    refine ⟨11664816496970898172606985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776544331313932115071323 11664816496970898172606985)
    ·
      refine ⟨8748612372728173629455239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11664816496970898172606985 8748612372728173629455239)
      ·
        refine ⟨13122918559092260444182859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748612372728173629455239 13122918559092260444182859)
        ·
          refine ⟨19684377838638390666274289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13122918559092260444182859 19684377838638390666274289)
          ·
            refine ⟨14763283378978792999705717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19684377838638390666274289 14763283378978792999705717)
            ·
              refine ⟨1384057816779261843722411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14763283378978792999705717 1384057816779261843722411)
              ·
                refine ⟨2076086725168892765583617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384057816779261843722411 2076086725168892765583617)
                ·
                  refine ⟨1557065043876669574187713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076086725168892765583617 1557065043876669574187713)
                  ·
                    refine ⟨1167798782907502180640785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557065043876669574187713 1167798782907502180640785)
                    ·
                      refine ⟨875849087180626635480589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167798782907502180640785 875849087180626635480589)
                      ·
                        rfl

theorem cell23_1705710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_1705710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705710 prefixEnd_1705710 := by exact prefixLift 1705710
  have htrace : WordTrace (prefixWord ++ tailWord_1705710) baseStart_1705710 baseEnd_1705710 := by
    simpa [prefixWord, tailWord_1705710, baseEnd_1705710] using wordTrace_append hprefix tailTrace_1705710
  have hstable : (prefixWord ++ tailWord_1705710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705710).length < 2 ^ (prefixWord ++ tailWord_1705710).sum := by decide
  have hdescent : baseEnd_1705710 < baseStart_1705710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705712 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_1705712 : Nat := 118140960795 + 1705712 * 2 ^ 59
def prefixEnd_1705712 : Nat := 4983230072969 + 3 ^ 40 * 1705712 * 2
def baseEnd_1705712 : Nat := 291950038047311875885193

theorem tailTrace_1705712 : CollatzResearch.WordTrace tailWord_1705712 prefixEnd_1705712 291950038047311875885193 := by
  unfold tailWord_1705712
  simp only [CollatzResearch.WordTrace]
  refine ⟨31106213798252105631071695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41474951731002807508095593 31106213798252105631071695)
  ·
    refine ⟨46659320697378158446607543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31106213798252105631071695 46659320697378158446607543)
    ·
      refine ⟨69988981046067237669911315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46659320697378158446607543 69988981046067237669911315)
      ·
        refine ⟨104983471569100856504866973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69988981046067237669911315 104983471569100856504866973)
        ·
          refine ⟨39368801838412821189325115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104983471569100856504866973 39368801838412821189325115)
          ·
            refine ⟨59053202757619231783987673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39368801838412821189325115 59053202757619231783987673)
            ·
              refine ⟨44289902068214423837990755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59053202757619231783987673 44289902068214423837990755)
              ·
                refine ⟨66434853102321635756986133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44289902068214423837990755 66434853102321635756986133)
                ·
                  refine ⟨3114133739171326676108725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66434853102321635756986133 3114133739171326676108725)
                  ·
                    refine ⟨291950038047311875885193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3114133739171326676108725 291950038047311875885193)
                    ·
                      rfl

theorem cell23_1705712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_1705712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705712 prefixEnd_1705712 := by exact prefixLift 1705712
  have htrace : WordTrace (prefixWord ++ tailWord_1705712) baseStart_1705712 baseEnd_1705712 := by
    simpa [prefixWord, tailWord_1705712, baseEnd_1705712] using wordTrace_append hprefix tailTrace_1705712
  have hstable : (prefixWord ++ tailWord_1705712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705712).length < 2 ^ (prefixWord ++ tailWord_1705712).sum := by decide
  have hdescent : baseEnd_1705712 < baseStart_1705712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705719 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 2, 5, 2]
def baseStart_1705719 : Nat := 118140960795 + 1705719 * 2 ^ 59
def prefixEnd_1705719 : Nat := 4983230072969 + 3 ^ 40 * 1705719 * 2
def baseEnd_1705719 : Nat := 875853708506517100268047

theorem tailTrace_1705719 : CollatzResearch.WordTrace tailWord_1705719 prefixEnd_1705719 875853708506517100268047 := by
  unfold tailWord_1705719
  simp only [CollatzResearch.WordTrace]
  refine ⟨62212682907478851457648211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41475121938319234305098807 62212682907478851457648211)
  ·
    refine ⟨93319024361218277186472317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62212682907478851457648211 93319024361218277186472317)
    ·
      refine ⟨34994634135456853944927119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93319024361218277186472317 34994634135456853944927119)
      ·
        refine ⟨52491951203185280917390679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34994634135456853944927119 52491951203185280917390679)
        ·
          refine ⟨78737926804777921376086019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52491951203185280917390679 78737926804777921376086019)
          ·
            refine ⟨118106890207166882064129029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78737926804777921376086019 118106890207166882064129029)
            ·
              refine ⟨22145041913843790387024193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118106890207166882064129029 22145041913843790387024193)
              ·
                refine ⟨16608781435382842790268145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22145041913843790387024193 16608781435382842790268145)
                ·
                  refine ⟨12456586076537132092701109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16608781435382842790268145 12456586076537132092701109)
                  ·
                    refine ⟨1167804944675356133690729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12456586076537132092701109 1167804944675356133690729)
                    ·
                      refine ⟨875853708506517100268047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167804944675356133690729 875853708506517100268047)
                      ·
                        rfl

theorem cell23_1705719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 5, 2].length) (baseStart_1705719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705719 prefixEnd_1705719 := by exact prefixLift 1705719
  have htrace : WordTrace (prefixWord ++ tailWord_1705719) baseStart_1705719 baseEnd_1705719 := by
    simpa [prefixWord, tailWord_1705719, baseEnd_1705719] using wordTrace_append hprefix tailTrace_1705719
  have hstable : (prefixWord ++ tailWord_1705719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705719).length < 2 ^ (prefixWord ++ tailWord_1705719).sum := by decide
  have hdescent : baseEnd_1705719 < baseStart_1705719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705722 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_1705722 : Nat := 118140960795 + 1705722 * 2 ^ 59
def prefixEnd_1705722 : Nat := 4983230072969 + 3 ^ 40 * 1705722 * 2
def baseEnd_1705722 : Nat := 875855248948480588530533

theorem tailTrace_1705722 : CollatzResearch.WordTrace tailWord_1705722 prefixEnd_1705722 875855248948480588530533 := by
  unfold tailWord_1705722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15553198081616995742501855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41475194884311988646671613 15553198081616995742501855)
  ·
    refine ⟨23329797122425493613752783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15553198081616995742501855 23329797122425493613752783)
    ·
      refine ⟨34994695683638240420629175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23329797122425493613752783 34994695683638240420629175)
      ·
        refine ⟨52492043525457360630943763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34994695683638240420629175 52492043525457360630943763)
        ·
          refine ⟨78738065288186040946415645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52492043525457360630943763 78738065288186040946415645)
          ·
            refine ⟨29526774483069765354905867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78738065288186040946415645 29526774483069765354905867)
            ·
              refine ⟨44290161724604648032358801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29526774483069765354905867 44290161724604648032358801)
              ·
                refine ⟨33217621293453486024269101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44290161724604648032358801 33217621293453486024269101)
                ·
                  refine ⟨12456607985045057259100913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33217621293453486024269101 12456607985045057259100913)
                  ·
                    refine ⟨9342455988783792944325685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12456607985045057259100913 9342455988783792944325685)
                    ·
                      refine ⟨875855248948480588530533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9342455988783792944325685 875855248948480588530533)
                      ·
                        rfl

theorem cell23_1705722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_1705722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705722 prefixEnd_1705722 := by exact prefixLift 1705722
  have htrace : WordTrace (prefixWord ++ tailWord_1705722) baseStart_1705722 baseEnd_1705722 := by
    simpa [prefixWord, tailWord_1705722, baseEnd_1705722] using wordTrace_append hprefix tailTrace_1705722
  have hstable : (prefixWord ++ tailWord_1705722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705722).length < 2 ^ (prefixWord ++ tailWord_1705722).sum := by decide
  have hdescent : baseEnd_1705722 < baseStart_1705722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705746 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_1705746 : Nat := 118140960795 + 1705746 * 2 ^ 59
def prefixEnd_1705746 : Nat := 4983230072969 + 3 ^ 40 * 1705746 * 2
def baseEnd_1705746 : Nat := 291955857494729498210141

theorem tailTrace_1705746 : CollatzResearch.WordTrace tailWord_1705746 prefixEnd_1705746 291955857494729498210141 := by
  unfold tailWord_1705746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15553416919595258767220273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41475778452254023379254061 15553416919595258767220273)
  ·
    refine ⟨11665062689696444075415205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15553416919595258767220273 11665062689696444075415205)
    ·
      refine ⟨2187199254318083264140351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11665062689696444075415205 2187199254318083264140351)
      ·
        refine ⟨3280798881477124896210527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187199254318083264140351 3280798881477124896210527)
        ·
          refine ⟨4921198322215687344315791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280798881477124896210527 4921198322215687344315791)
          ·
            refine ⟨7381797483323531016473687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921198322215687344315791 7381797483323531016473687)
            ·
              refine ⟨11072696224985296524710531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381797483323531016473687 11072696224985296524710531)
              ·
                refine ⟨16609044337477944787065797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11072696224985296524710531 16609044337477944787065797)
                ·
                  refine ⟨3114195813277114647574837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16609044337477944787065797 3114195813277114647574837)
                  ·
                    refine ⟨291955857494729498210141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3114195813277114647574837 291955857494729498210141)
                    ·
                      rfl

theorem cell23_1705746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_1705746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705746 prefixEnd_1705746 := by exact prefixLift 1705746
  have htrace : WordTrace (prefixWord ++ tailWord_1705746) baseStart_1705746 baseEnd_1705746 := by
    simpa [prefixWord, tailWord_1705746, baseEnd_1705746] using wordTrace_append hprefix tailTrace_1705746
  have hstable : (prefixWord ++ tailWord_1705746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705746).length < 2 ^ (prefixWord ++ tailWord_1705746).sum := by decide
  have hdescent : baseEnd_1705746 < baseStart_1705746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705749 : List Nat := [1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_1705749 : Nat := 118140960795 + 1705749 * 2 ^ 59
def prefixEnd_1705749 : Nat := 4983230072969 + 3 ^ 40 * 1705749 * 2
def baseEnd_1705749 : Nat := 875869112926151982892909

theorem tailTrace_1705749 : CollatzResearch.WordTrace tailWord_1705749 prefixEnd_1705749 875869112926151982892909 := by
  unfold tailWord_1705749
  simp only [CollatzResearch.WordTrace]
  refine ⟨62213777097370166581240301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41475851398246777720826867 62213777097370166581240301)
  ·
    refine ⟨23330166411513812467965113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62213777097370166581240301 23330166411513812467965113)
    ·
      refine ⟨17497624808635359350973835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23330166411513812467965113 17497624808635359350973835)
      ·
        refine ⟨26246437212953039026460753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17497624808635359350973835 26246437212953039026460753)
        ·
          refine ⟨19684827909714779269845565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26246437212953039026460753 19684827909714779269845565)
          ·
            refine ⟨7381810466143042226192087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19684827909714779269845565 7381810466143042226192087)
            ·
              refine ⟨11072715699214563339288131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381810466143042226192087 11072715699214563339288131)
              ·
                refine ⟨16609073548821845008932197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11072715699214563339288131 16609073548821845008932197)
                ·
                  refine ⟨3114201290404095939174787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16609073548821845008932197 3114201290404095939174787)
                  ·
                    refine ⟨4671301935606143908762181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3114201290404095939174787 4671301935606143908762181)
                    ·
                      refine ⟨875869112926151982892909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4671301935606143908762181 875869112926151982892909)
                      ·
                        rfl

theorem cell23_1705749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_1705749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705749 prefixEnd_1705749 := by exact prefixLift 1705749
  have htrace : WordTrace (prefixWord ++ tailWord_1705749) baseStart_1705749 baseEnd_1705749 := by
    simpa [prefixWord, tailWord_1705749, baseEnd_1705749] using wordTrace_append hprefix tailTrace_1705749
  have hstable : (prefixWord ++ tailWord_1705749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705749).length < 2 ^ (prefixWord ++ tailWord_1705749).sum := by decide
  have hdescent : baseEnd_1705749 < baseStart_1705749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705786 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_1705786 : Nat := 118140960795 + 1705786 * 2 ^ 59
def prefixEnd_1705786 : Nat := 4983230072969 + 3 ^ 40 * 1705786 * 2
def baseEnd_1705786 : Nat := 875888111710368338130239

theorem tailTrace_1705786 : CollatzResearch.WordTrace tailWord_1705786 prefixEnd_1705786 875888111710368338130239 := by
  unfold tailWord_1705786
  simp only [CollatzResearch.WordTrace]
  refine ⟨15553781649559030475084303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41476751065490747933558141 15553781649559030475084303)
  ·
    refine ⟨23330672474338545712626455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15553781649559030475084303 23330672474338545712626455)
    ·
      refine ⟨34996008711507818568939683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23330672474338545712626455 34996008711507818568939683)
      ·
        refine ⟨52494013067261727853409525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34996008711507818568939683 52494013067261727853409525)
        ·
          refine ⟨4921313725055786986257143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52494013067261727853409525 4921313725055786986257143)
          ·
            refine ⟨7381970587583680479385715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921313725055786986257143 7381970587583680479385715)
            ·
              refine ⟨11072955881375520719078573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381970587583680479385715 11072955881375520719078573)
              ·
                refine ⟨4152358455515820269654465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11072955881375520719078573 4152358455515820269654465)
                ·
                  refine ⟨3114268841636865202240849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4152358455515820269654465 3114268841636865202240849)
                  ·
                    refine ⟨2335701631227648901680637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3114268841636865202240849 2335701631227648901680637)
                    ·
                      refine ⟨875888111710368338130239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335701631227648901680637 875888111710368338130239)
                      ·
                        rfl

theorem cell23_1705786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_1705786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705786 prefixEnd_1705786 := by exact prefixLift 1705786
  have htrace : WordTrace (prefixWord ++ tailWord_1705786) baseStart_1705786 baseEnd_1705786 := by
    simpa [prefixWord, tailWord_1705786, baseEnd_1705786] using wordTrace_append hprefix tailTrace_1705786
  have hstable : (prefixWord ++ tailWord_1705786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705786).length < 2 ^ (prefixWord ++ tailWord_1705786).sum := by decide
  have hdescent : baseEnd_1705786 < baseStart_1705786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705792 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1705792 : Nat := 118140960795 + 1705792 * 2 ^ 59
def prefixEnd_1705792 : Nat := 4983230072969 + 3 ^ 40 * 1705792 * 2
def baseEnd_1705792 : Nat := 875891192594295314655211

theorem tailTrace_1705792 : CollatzResearch.WordTrace tailWord_1705792 prefixEnd_1705792 875891192594295314655211 := by
  unfold tailWord_1705792
  simp only [CollatzResearch.WordTrace]
  refine ⟨31107672718107192462527815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41476896957476256616703753 31107672718107192462527815)
  ·
    refine ⟨46661509077160788693791723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31107672718107192462527815 46661509077160788693791723)
    ·
      refine ⟨69992263615741183040687585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46661509077160788693791723 69992263615741183040687585)
      ·
        refine ⟨52494197711805887280515689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69992263615741183040687585 52494197711805887280515689)
        ·
          refine ⟨39370648283854415460386767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52494197711805887280515689 39370648283854415460386767)
          ·
            refine ⟨59055972425781623190580151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39370648283854415460386767 59055972425781623190580151)
            ·
              refine ⟨88583958638672434785870227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59055972425781623190580151 88583958638672434785870227)
              ·
                refine ⟨132875937958008652178805341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88583958638672434785870227 132875937958008652178805341)
                ·
                  refine ⟨49828476734253244567052003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132875937958008652178805341 49828476734253244567052003)
                  ·
                    refine ⟨74742715101379866850578005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49828476734253244567052003 74742715101379866850578005)
                    ·
                      refine ⟨875891192594295314655211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 74742715101379866850578005 875891192594295314655211)
                      ·
                        rfl

theorem cell23_1705792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1705792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705792 prefixEnd_1705792 := by exact prefixLift 1705792
  have htrace : WordTrace (prefixWord ++ tailWord_1705792) baseStart_1705792 baseEnd_1705792 := by
    simpa [prefixWord, tailWord_1705792, baseEnd_1705792] using wordTrace_append hprefix tailTrace_1705792
  have hstable : (prefixWord ++ tailWord_1705792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705792).length < 2 ^ (prefixWord ++ tailWord_1705792).sum := by decide
  have hdescent : baseEnd_1705792 < baseStart_1705792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705810 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1705810 : Nat := 118140960795 + 1705810 * 2 ^ 59
def prefixEnd_1705810 : Nat := 4983230072969 + 3 ^ 40 * 1705810 * 2
def baseEnd_1705810 : Nat := 291966811748692081410043

theorem tailTrace_1705810 : CollatzResearch.WordTrace tailWord_1705810 prefixEnd_1705810 291966811748692081410043 := by
  unfold tailWord_1705810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15554000487537293499802721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41477334633432782666140589 15554000487537293499802721)
  ·
    refine ⟨11665500365652970124852041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15554000487537293499802721 11665500365652970124852041)
    ·
      refine ⟨8749125274239727593639031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11665500365652970124852041 8749125274239727593639031)
      ·
        refine ⟨13123687911359591390458547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8749125274239727593639031 13123687911359591390458547)
        ·
          refine ⟨19685531867039387085687821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13123687911359591390458547 19685531867039387085687821)
          ·
            refine ⟨7382074450139770157132933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19685531867039387085687821 7382074450139770157132933)
            ·
              refine ⟨1384138959401206904462425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7382074450139770157132933 1384138959401206904462425)
              ·
                refine ⟨1038104219550905178346819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384138959401206904462425 1038104219550905178346819)
                ·
                  refine ⟨1557156329326357767520229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038104219550905178346819 1557156329326357767520229)
                  ·
                    refine ⟨291966811748692081410043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557156329326357767520229 291966811748692081410043)
                    ·
                      rfl

theorem cell23_1705810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1705810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705810 prefixEnd_1705810 := by exact prefixLift 1705810
  have htrace : WordTrace (prefixWord ++ tailWord_1705810) baseStart_1705810 baseEnd_1705810 := by
    simpa [prefixWord, tailWord_1705810, baseEnd_1705810] using wordTrace_append hprefix tailTrace_1705810
  have hstable : (prefixWord ++ tailWord_1705810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705810).length < 2 ^ (prefixWord ++ tailWord_1705810).sum := by decide
  have hdescent : baseEnd_1705810 < baseStart_1705810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705849 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 1, 6]
def baseStart_1705849 : Nat := 118140960795 + 1705849 * 2 ^ 59
def prefixEnd_1705849 : Nat := 4983230072969 + 3 ^ 40 * 1705849 * 2
def baseEnd_1705849 : Nat := 291973486997200530547483

theorem tailTrace_1705849 : CollatzResearch.WordTrace tailWord_1705849 prefixEnd_1705849 291973486997200530547483 := by
  unfold tailWord_1705849
  simp only [CollatzResearch.WordTrace]
  refine ⟨62217424397007883659880601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41478282931338589106587067 62217424397007883659880601)
  ·
    refine ⟨46663068297755912744910451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62217424397007883659880601 46663068297755912744910451)
    ·
      refine ⟨69994602446633869117365677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46663068297755912744910451 69994602446633869117365677)
      ·
        refine ⟨26247975917487700919012129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69994602446633869117365677 26247975917487700919012129)
        ·
          refine ⟨19685981938115775689259097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26247975917487700919012129 19685981938115775689259097)
          ·
            refine ⟨14764486453586831766944323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19685981938115775689259097 14764486453586831766944323)
            ·
              refine ⟨22146729680380247650416485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14764486453586831766944323 22146729680380247650416485)
              ·
                refine ⟨4152511815071296434453091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22146729680380247650416485 4152511815071296434453091)
                ·
                  refine ⟨6228767722606944651679637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152511815071296434453091 6228767722606944651679637)
                  ·
                    refine ⟨291973486997200530547483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6228767722606944651679637 291973486997200530547483)
                    ·
                      rfl

theorem cell23_1705849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 6].length) (baseStart_1705849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705849 prefixEnd_1705849 := by exact prefixLift 1705849
  have htrace : WordTrace (prefixWord ++ tailWord_1705849) baseStart_1705849 baseEnd_1705849 := by
    simpa [prefixWord, tailWord_1705849, baseEnd_1705849] using wordTrace_append hprefix tailTrace_1705849
  have hstable : (prefixWord ++ tailWord_1705849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705849).length < 2 ^ (prefixWord ++ tailWord_1705849).sum := by decide
  have hdescent : baseEnd_1705849 < baseStart_1705849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705856 : List Nat := [2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4]
def baseStart_1705856 : Nat := 118140960795 + 1705856 * 2 ^ 59
def prefixEnd_1705856 : Nat := 4983230072969 + 3 ^ 40 * 1705856 * 2
def baseEnd_1705856 : Nat := 875924055356183064254917

theorem tailTrace_1705856 : CollatzResearch.WordTrace tailWord_1705856 prefixEnd_1705856 875924055356183064254917 := by
  unfold tailWord_1705856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31108839853991261927692711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41478453138655015903590281 31108839853991261927692711)
  ·
    refine ⟨46663259780986892891539067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31108839853991261927692711 46663259780986892891539067)
    ·
      refine ⟨69994889671480339337308601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46663259780986892891539067 69994889671480339337308601)
      ·
        refine ⟨52496167253610254502981451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69994889671480339337308601 52496167253610254502981451)
        ·
          refine ⟨78744250880415381754472177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52496167253610254502981451 78744250880415381754472177)
          ·
            refine ⟨59058188160311536315854133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78744250880415381754472177 59058188160311536315854133)
            ·
              refine ⟨5536705140029206529611325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59058188160311536315854133 5536705140029206529611325)
              ·
                refine ⟨2076264427510952448604247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5536705140029206529611325 2076264427510952448604247)
                ·
                  refine ⟨3114396641266428672906371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076264427510952448604247 3114396641266428672906371)
                  ·
                    refine ⟨4671594961899643009359557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3114396641266428672906371 4671594961899643009359557)
                    ·
                      refine ⟨875924055356183064254917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4671594961899643009359557 875924055356183064254917)
                      ·
                        rfl

theorem cell23_1705856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_1705856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705856 prefixEnd_1705856 := by exact prefixLift 1705856
  have htrace : WordTrace (prefixWord ++ tailWord_1705856) baseStart_1705856 baseEnd_1705856 := by
    simpa [prefixWord, tailWord_1705856, baseEnd_1705856] using wordTrace_append hprefix tailTrace_1705856
  have hstable : (prefixWord ++ tailWord_1705856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705856).length < 2 ^ (prefixWord ++ tailWord_1705856).sum := by decide
  have hdescent : baseEnd_1705856 < baseStart_1705856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705873 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 3, 2, 2]
def baseStart_1705873 : Nat := 118140960795 + 1705873 * 2 ^ 59
def prefixEnd_1705873 : Nat := 4983230072969 + 3 ^ 40 * 1705873 * 2
def baseEnd_1705873 : Nat := 875932784527309497742339

theorem tailTrace_1705873 : CollatzResearch.WordTrace tailWord_1705873 prefixEnd_1705873 875932784527309497742339 := by
  unfold tailWord_1705873
  simp only [CollatzResearch.WordTrace]
  refine ⟨62218299748920935758754273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41478866499280623839169515 62218299748920935758754273)
  ·
    refine ⟨46663724811690701819065705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62218299748920935758754273 46663724811690701819065705)
    ·
      refine ⟨34997793608768026364299279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46663724811690701819065705 34997793608768026364299279)
      ·
        refine ⟨52496690413152039546448919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34997793608768026364299279 52496690413152039546448919)
        ·
          refine ⟨78745035619728059319673379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52496690413152039546448919 78745035619728059319673379)
          ·
            refine ⟨118117553429592088979510069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78745035619728059319673379 118117553429592088979510069)
            ·
              refine ⟨11073520634024258341829069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118117553429592088979510069 11073520634024258341829069)
              ·
                refine ⟨4152570237759096878185901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11073520634024258341829069 4152570237759096878185901)
                ·
                  refine ⟨1557213839159661329319713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4152570237759096878185901 1557213839159661329319713)
                  ·
                    refine ⟨1167910379369745996989785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557213839159661329319713 1167910379369745996989785)
                    ·
                      refine ⟨875932784527309497742339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167910379369745996989785 875932784527309497742339)
                      ·
                        rfl

theorem cell23_1705873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 2, 2].length) (baseStart_1705873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705873 prefixEnd_1705873 := by exact prefixLift 1705873
  have htrace : WordTrace (prefixWord ++ tailWord_1705873) baseStart_1705873 baseEnd_1705873 := by
    simpa [prefixWord, tailWord_1705873, baseEnd_1705873] using wordTrace_append hprefix tailTrace_1705873
  have hstable : (prefixWord ++ tailWord_1705873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705873).length < 2 ^ (prefixWord ++ tailWord_1705873).sum := by decide
  have hdescent : baseEnd_1705873 < baseStart_1705873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705876 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1705876 : Nat := 118140960795 + 1705876 * 2 ^ 59
def prefixEnd_1705876 : Nat := 4983230072969 + 3 ^ 40 * 1705876 * 2
def baseEnd_1705876 : Nat := 875934324969272986004825

theorem tailTrace_1705876 : CollatzResearch.WordTrace tailWord_1705876 prefixEnd_1705876 875934324969272986004825 := by
  unfold tailWord_1705876
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109204583955033635556741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41478939445273378180742321 31109204583955033635556741)
  ·
    refine ⟨5832975859491568806666889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31109204583955033635556741 5832975859491568806666889)
    ·
      refine ⟨4374731894618676605000167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5832975859491568806666889 4374731894618676605000167)
      ·
        refine ⟨6562097841928014907500251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374731894618676605000167 6562097841928014907500251)
        ·
          refine ⟨9843146762892022361250377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6562097841928014907500251 9843146762892022361250377)
          ·
            refine ⟨7382360072169016770937783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9843146762892022361250377 7382360072169016770937783)
            ·
              refine ⟨11073540108253525156406675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7382360072169016770937783 11073540108253525156406675)
              ·
                refine ⟨16610310162380287734610013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11073540108253525156406675 16610310162380287734610013)
                ·
                  refine ⟨6228866310892607900478755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16610310162380287734610013 6228866310892607900478755)
                  ·
                    refine ⟨9343299466338911850718133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6228866310892607900478755 9343299466338911850718133)
                    ·
                      refine ⟨875934324969272986004825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9343299466338911850718133 875934324969272986004825)
                      ·
                        rfl

theorem cell23_1705876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1705876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705876 prefixEnd_1705876 := by exact prefixLift 1705876
  have htrace : WordTrace (prefixWord ++ tailWord_1705876) baseStart_1705876 baseEnd_1705876 := by
    simpa [prefixWord, tailWord_1705876, baseEnd_1705876] using wordTrace_append hprefix tailTrace_1705876
  have hstable : (prefixWord ++ tailWord_1705876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705876).length < 2 ^ (prefixWord ++ tailWord_1705876).sum := by decide
  have hdescent : baseEnd_1705876 < baseStart_1705876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705890 : List Nat := [3, 3, 1, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_1705890 : Nat := 118140960795 + 1705890 * 2 ^ 59
def prefixEnd_1705890 : Nat := 4983230072969 + 3 ^ 40 * 1705890 * 2
def baseEnd_1705890 : Nat := 875941513698435931229761

theorem tailTrace_1705890 : CollatzResearch.WordTrace tailWord_1705890 prefixEnd_1705890 875941513698435931229761 := by
  unfold tailWord_1705890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15554729947464836915530781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41479279859906231774748749 15554729947464836915530781)
  ·
    refine ⟨5833023730299313843324043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15554729947464836915530781 5833023730299313843324043)
    ·
      refine ⟨8749535595448970764986065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5833023730299313843324043 8749535595448970764986065)
      ·
        refine ⟨6562151696586728073739549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8749535595448970764986065 6562151696586728073739549)
        ·
          refine ⟨2460806886220023027652331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6562151696586728073739549 2460806886220023027652331)
          ·
            refine ⟨3691210329330034541478497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460806886220023027652331 3691210329330034541478497)
            ·
              refine ⟨2768407746997525906108873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691210329330034541478497 2768407746997525906108873)
              ·
                refine ⟨2076305810248144429581655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768407746997525906108873 2076305810248144429581655)
                ·
                  refine ⟨3114458715372216644372483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076305810248144429581655 3114458715372216644372483)
                  ·
                    refine ⟨4671688073058324966558725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3114458715372216644372483 4671688073058324966558725)
                    ·
                      refine ⟨875941513698435931229761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4671688073058324966558725 875941513698435931229761)
                      ·
                        rfl

theorem cell23_1705890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_1705890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705890 prefixEnd_1705890 := by exact prefixLift 1705890
  have htrace : WordTrace (prefixWord ++ tailWord_1705890) baseStart_1705890 baseEnd_1705890 := by
    simpa [prefixWord, tailWord_1705890, baseEnd_1705890] using wordTrace_append hprefix tailTrace_1705890
  have hstable : (prefixWord ++ tailWord_1705890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705890).length < 2 ^ (prefixWord ++ tailWord_1705890).sum := by decide
  have hdescent : baseEnd_1705890 < baseStart_1705890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705906 : List Nat := [3, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1705906 : Nat := 118140960795 + 1705906 * 2 ^ 59
def prefixEnd_1705906 : Nat := 4983230072969 + 3 ^ 40 * 1705906 * 2
def baseEnd_1705906 : Nat := 875949729388907868629687

theorem tailTrace_1705906 : CollatzResearch.WordTrace tailWord_1705906 prefixEnd_1705906 875949729388907868629687 := by
  unfold tailWord_1705906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15554875839450345598676393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41479668905200921596470381 15554875839450345598676393)
  ·
    refine ⟨11666156879587759199007295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15554875839450345598676393 11666156879587759199007295)
    ·
      refine ⟨17499235319381638798510943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11666156879587759199007295 17499235319381638798510943)
      ·
        refine ⟨26248852979072458197766415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17499235319381638798510943 26248852979072458197766415)
        ·
          refine ⟨39373279468608687296649623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26248852979072458197766415 39373279468608687296649623)
          ·
            refine ⟨59059919202913030944974435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39373279468608687296649623 59059919202913030944974435)
            ·
              refine ⟨88589878804369546417461653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59059919202913030944974435 88589878804369546417461653)
              ·
                refine ⟨4152650568954822488318515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88589878804369546417461653 4152650568954822488318515)
                ·
                  refine ⟨6228975853432233732477773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152650568954822488318515 6228975853432233732477773)
                  ·
                    refine ⟨2335865945037087649679165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6228975853432233732477773 2335865945037087649679165)
                    ·
                      refine ⟨875949729388907868629687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335865945037087649679165 875949729388907868629687)
                      ·
                        rfl

theorem cell23_1705906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1705906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705906 prefixEnd_1705906 := by exact prefixLift 1705906
  have htrace : WordTrace (prefixWord ++ tailWord_1705906) baseStart_1705906 baseEnd_1705906 := by
    simpa [prefixWord, tailWord_1705906, baseEnd_1705906] using wordTrace_append hprefix tailTrace_1705906
  have hstable : (prefixWord ++ tailWord_1705906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705906).length < 2 ^ (prefixWord ++ tailWord_1705906).sum := by decide
  have hdescent : baseEnd_1705906 < baseStart_1705906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705919 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1705919 : Nat := 118140960795 + 1705919 * 2 ^ 59
def prefixEnd_1705919 : Nat := 4983230072969 + 3 ^ 40 * 1705919 * 2
def baseEnd_1705919 : Nat := 875956404637416317767127

theorem tailTrace_1705919 : CollatzResearch.WordTrace tailWord_1705919 prefixEnd_1705919 875956404637416317767127 := by
  unfold tailWord_1705919
  simp only [CollatzResearch.WordTrace]
  refine ⟨62219977506754285614928811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41479985004502857076619207 62219977506754285614928811)
  ·
    refine ⟨93329966260131428422393217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62219977506754285614928811 93329966260131428422393217)
    ·
      refine ⟨69997474695098571316794913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93329966260131428422393217 69997474695098571316794913)
      ·
        refine ⟨52498106021323928487596185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69997474695098571316794913 52498106021323928487596185)
        ·
          refine ⟨39373579515992946365697139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52498106021323928487596185 39373579515992946365697139)
          ·
            refine ⟨59060369273989419548545709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39373579515992946365697139 59060369273989419548545709)
            ·
              refine ⟨22147638477746032330704641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59060369273989419548545709 22147638477746032330704641)
              ·
                refine ⟨16610728858309524248028481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22147638477746032330704641 16610728858309524248028481)
                ·
                  refine ⟨12458046643732143186021361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16610728858309524248028481 12458046643732143186021361)
                  ·
                    refine ⟨9343534982799107389516021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12458046643732143186021361 9343534982799107389516021)
                    ·
                      refine ⟨875956404637416317767127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9343534982799107389516021 875956404637416317767127)
                      ·
                        rfl

theorem cell23_1705919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1705919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705919 prefixEnd_1705919 := by exact prefixLift 1705919
  have htrace : WordTrace (prefixWord ++ tailWord_1705919) baseStart_1705919 baseEnd_1705919 := by
    simpa [prefixWord, tailWord_1705919, baseEnd_1705919] using wordTrace_append hprefix tailTrace_1705919
  have hstable : (prefixWord ++ tailWord_1705919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705919).length < 2 ^ (prefixWord ++ tailWord_1705919).sum := by decide
  have hdescent : baseEnd_1705919 < baseStart_1705919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705929 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 4]
def baseStart_1705929 : Nat := 118140960795 + 1705929 * 2 ^ 59
def prefixEnd_1705929 : Nat := 4983230072969 + 3 ^ 40 * 1705929 * 2
def baseEnd_1705929 : Nat := 875961539443961278642081

theorem tailTrace_1705929 : CollatzResearch.WordTrace tailWord_1705929 prefixEnd_1705929 875961539443961278642081 := by
  unfold tailWord_1705929
  simp only [CollatzResearch.WordTrace]
  refine ⟨62220342236718057322792841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41480228157812038215195227 62220342236718057322792841)
  ·
    refine ⟨46665256677538542992094631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62220342236718057322792841 46665256677538542992094631)
    ·
      refine ⟨69997885016307814488141947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46665256677538542992094631 69997885016307814488141947)
      ·
        refine ⟨104996827524461721732212921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69997885016307814488141947 104996827524461721732212921)
        ·
          refine ⟨78747620643346291299159691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104996827524461721732212921 78747620643346291299159691)
          ·
            refine ⟨118121430965019436948739537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78747620643346291299159691 118121430965019436948739537)
            ·
              refine ⟨88591073223764577711554653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118121430965019436948739537 88591073223764577711554653)
              ·
                refine ⟨33221652458911716641832995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88591073223764577711554653 33221652458911716641832995)
                ·
                  refine ⟨49832478688367574962749493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33221652458911716641832995 49832478688367574962749493)
                  ·
                    refine ⟨4671794877034460152757765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49832478688367574962749493 4671794877034460152757765)
                    ·
                      refine ⟨875961539443961278642081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4671794877034460152757765 875961539443961278642081)
                      ·
                        rfl

theorem cell23_1705929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_1705929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705929 prefixEnd_1705929 := by exact prefixLift 1705929
  have htrace : WordTrace (prefixWord ++ tailWord_1705929) baseStart_1705929 baseEnd_1705929 := by
    simpa [prefixWord, tailWord_1705929, baseEnd_1705929] using wordTrace_append hprefix tailTrace_1705929
  have hstable : (prefixWord ++ tailWord_1705929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705929).length < 2 ^ (prefixWord ++ tailWord_1705929).sum := by decide
  have hdescent : baseEnd_1705929 < baseStart_1705929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705940 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1705940 : Nat := 118140960795 + 1705940 * 2 ^ 59
def prefixEnd_1705940 : Nat := 4983230072969 + 3 ^ 40 * 1705940 * 2
def baseEnd_1705940 : Nat := 875967187731160735604531

theorem tailTrace_1705940 : CollatzResearch.WordTrace tailWord_1705940 prefixEnd_1705940 875967187731160735604531 := by
  unfold tailWord_1705940
  simp only [CollatzResearch.WordTrace]
  refine ⟨31110371719839103100721637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41480495626452137467628849 31110371719839103100721637)
  ·
    refine ⟨5833194697469831831385307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31110371719839103100721637 5833194697469831831385307)
    ·
      refine ⟨8749792046204747747077961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5833194697469831831385307 8749792046204747747077961)
      ·
        refine ⟨6562344034653560810308471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8749792046204747747077961 6562344034653560810308471)
        ·
          refine ⟨9843516051980341215462707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6562344034653560810308471 9843516051980341215462707)
          ·
            refine ⟨14765274077970511823194061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9843516051980341215462707 14765274077970511823194061)
            ·
              refine ⟨5536977779238941933697773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14765274077970511823194061 5536977779238941933697773)
              ·
                refine ⟨2076366667214603225136665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5536977779238941933697773 2076366667214603225136665)
                ·
                  refine ⟨1557275000410952418852499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076366667214603225136665 1557275000410952418852499)
                  ·
                    refine ⟨2335912500616428628278749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1557275000410952418852499 2335912500616428628278749)
                    ·
                      refine ⟨875967187731160735604531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2335912500616428628278749 875967187731160735604531)
                      ·
                        rfl

theorem cell23_1705940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1705940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705940 prefixEnd_1705940 := by exact prefixLift 1705940
  have htrace : WordTrace (prefixWord ++ tailWord_1705940) baseStart_1705940 baseEnd_1705940 := by
    simpa [prefixWord, tailWord_1705940, baseEnd_1705940] using wordTrace_append hprefix tailTrace_1705940
  have hstable : (prefixWord ++ tailWord_1705940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705940).length < 2 ^ (prefixWord ++ tailWord_1705940).sum := by decide
  have hdescent : baseEnd_1705940 < baseStart_1705940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705963 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 6, 2, 2]
def baseStart_1705963 : Nat := 118140960795 + 1705963 * 2 ^ 59
def prefixEnd_1705963 : Nat := 4983230072969 + 3 ^ 40 * 1705963 * 2
def baseEnd_1705963 : Nat := 875978997786214145616925

theorem tailTrace_1705963 : CollatzResearch.WordTrace tailWord_1705963 prefixEnd_1705963 875978997786214145616925 := by
  unfold tailWord_1705963
  simp only [CollatzResearch.WordTrace]
  refine ⟨62221582318594881129530543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41481054879063254086353695 62221582318594881129530543)
  ·
    refine ⟨93332373477892321694295815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62221582318594881129530543 93332373477892321694295815)
    ·
      refine ⟨139998560216838482541443723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93332373477892321694295815 139998560216838482541443723)
      ·
        refine ⟨209997840325257723812165585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139998560216838482541443723 209997840325257723812165585)
        ·
          refine ⟨157498380243943292859124189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209997840325257723812165585 157498380243943292859124189)
          ·
            refine ⟨59061892591478734822171571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157498380243943292859124189 59061892591478734822171571)
            ·
              refine ⟨88592838887218102233257357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59061892591478734822171571 88592838887218102233257357)
              ·
                refine ⟨33222314582706788337471509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88592838887218102233257357 33222314582706788337471509)
                ·
                  refine ⟨1557295996064380703318977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33222314582706788337471509 1557295996064380703318977)
                  ·
                    refine ⟨1167971997048285527489233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557295996064380703318977 1167971997048285527489233)
                    ·
                      refine ⟨875978997786214145616925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1167971997048285527489233 875978997786214145616925)
                      ·
                        rfl

theorem cell23_1705963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 2, 2].length) (baseStart_1705963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705963 prefixEnd_1705963 := by exact prefixLift 1705963
  have htrace : WordTrace (prefixWord ++ tailWord_1705963) baseStart_1705963 baseEnd_1705963 := by
    simpa [prefixWord, tailWord_1705963, baseEnd_1705963] using wordTrace_append hprefix tailTrace_1705963
  have hstable : (prefixWord ++ tailWord_1705963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705963).length < 2 ^ (prefixWord ++ tailWord_1705963).sum := by decide
  have hdescent : baseEnd_1705963 < baseStart_1705963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1705979 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_1705979 : Nat := 118140960795 + 1705979 * 2 ^ 59
def prefixEnd_1705979 : Nat := 4983230072969 + 3 ^ 40 * 1705979 * 2
def baseEnd_1705979 : Nat := 875987213476686083016851

theorem tailTrace_1705979 : CollatzResearch.WordTrace tailWord_1705979 prefixEnd_1705979 875987213476686083016851 := by
  unfold tailWord_1705979
  simp only [CollatzResearch.WordTrace]
  refine ⟨62222165886536915862112991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41481443924357943908075327 62222165886536915862112991)
  ·
    refine ⟨93333248829805373793169487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62222165886536915862112991 93333248829805373793169487)
    ·
      refine ⟨139999873244708060689754231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93333248829805373793169487 139999873244708060689754231)
      ·
        refine ⟨209999809867062091034631347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139999873244708060689754231 209999809867062091034631347)
        ·
          refine ⟨314999714800593136551947021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209999809867062091034631347 314999714800593136551947021)
          ·
            refine ⟨118124893050222426206980133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314999714800593136551947021 118124893050222426206980133)
            ·
              refine ⟨22148417446916704913808775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118124893050222426206980133 22148417446916704913808775)
              ·
                refine ⟨33222626170375057370713163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22148417446916704913808775 33222626170375057370713163)
                ·
                  refine ⟨49833939255562586056069745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33222626170375057370713163 49833939255562586056069745)
                  ·
                    refine ⟨37375454441671939542052309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49833939255562586056069745 37375454441671939542052309)
                    ·
                      refine ⟨875987213476686083016851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37375454441671939542052309 875987213476686083016851)
                      ·
                        rfl

theorem cell23_1705979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_1705979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1705979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1705979 prefixEnd_1705979 := by exact prefixLift 1705979
  have htrace : WordTrace (prefixWord ++ tailWord_1705979) baseStart_1705979 baseEnd_1705979 := by
    simpa [prefixWord, tailWord_1705979, baseEnd_1705979] using wordTrace_append hprefix tailTrace_1705979
  have hstable : (prefixWord ++ tailWord_1705979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1705979).length < 2 ^ (prefixWord ++ tailWord_1705979).sum := by decide
  have hdescent : baseEnd_1705979 < baseStart_1705979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1705979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706073 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 3]
def baseStart_1706073 : Nat := 118140960795 + 1706073 * 2 ^ 59
def prefixEnd_1706073 : Nat := 4983230072969 + 3 ^ 40 * 1706073 * 2
def baseEnd_1706073 : Nat := 876035480658208715241419

theorem tailTrace_1706073 : CollatzResearch.WordTrace tailWord_1706073 prefixEnd_1706073 876035480658208715241419 := by
  unfold tailWord_1706073
  simp only [CollatzResearch.WordTrace]
  refine ⟨62225594348196369916034873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41483729565464246610689915 62225594348196369916034873)
  ·
    refine ⟨46669195761147277437026155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62225594348196369916034873 46669195761147277437026155)
    ·
      refine ⟨70003793641720916155539233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46669195761147277437026155 70003793641720916155539233)
      ·
        refine ⟨52502845231290687116654425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70003793641720916155539233 52502845231290687116654425)
        ·
          refine ⟨39377133923468015337490819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52502845231290687116654425 39377133923468015337490819)
          ·
            refine ⟨59065700885202023006236229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39377133923468015337490819 59065700885202023006236229)
            ·
              refine ⟨11074818915975379313669293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59065700885202023006236229 11074818915975379313669293)
              ·
                refine ⟨4153057093490767242625985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11074818915975379313669293 4153057093490767242625985)
                ·
                  refine ⟨3114792820118075431969489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153057093490767242625985 3114792820118075431969489)
                  ·
                    refine ⟨2336094615088556573977117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3114792820118075431969489 2336094615088556573977117)
                    ·
                      refine ⟨876035480658208715241419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2336094615088556573977117 876035480658208715241419)
                      ·
                        rfl

theorem cell23_1706073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_1706073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706073 prefixEnd_1706073 := by exact prefixLift 1706073
  have htrace : WordTrace (prefixWord ++ tailWord_1706073) baseStart_1706073 baseEnd_1706073 := by
    simpa [prefixWord, tailWord_1706073, baseEnd_1706073] using wordTrace_append hprefix tailTrace_1706073
  have hstable : (prefixWord ++ tailWord_1706073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706073).length < 2 ^ (prefixWord ++ tailWord_1706073).sum := by decide
  have hdescent : baseEnd_1706073 < baseStart_1706073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706093 : List Nat := [1, 5, 1, 1, 2, 1, 2, 4, 6]
def baseStart_1706093 : Nat := 118140960795 + 1706093 * 2 ^ 59
def prefixEnd_1706093 : Nat := 4983230072969 + 3 ^ 40 * 1706093 * 2
def baseEnd_1706093 : Nat := 97338416696810959665703

theorem tailTrace_1706093 : CollatzResearch.WordTrace tailWord_1706093 prefixEnd_1706093 97338416696810959665703 := by
  unfold tailWord_1706093
  simp only [CollatzResearch.WordTrace]
  refine ⟨62226323808123913331762933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41484215872082608887841955 62226323808123913331762933)
  ·
    refine ⟨5833717857011616874852775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62226323808123913331762933 5833717857011616874852775)
    ·
      refine ⟨8750576785517425312279163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5833717857011616874852775 8750576785517425312279163)
      ·
        refine ⟨13125865178276137968418745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8750576785517425312279163 13125865178276137968418745)
        ·
          refine ⟨9844398883707103476314059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13125865178276137968418745 9844398883707103476314059)
          ·
            refine ⟨14766598325560655214471089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844398883707103476314059 14766598325560655214471089)
            ·
              refine ⟨11074948744170491410853317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14766598325560655214471089 11074948744170491410853317)
              ·
                refine ⟨2076552889531967139534997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11074948744170491410853317 2076552889531967139534997)
                ·
                  refine ⟨97338416696810959665703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2076552889531967139534997 97338416696810959665703)
                  ·
                    rfl

theorem cell23_1706093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_1706093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706093 prefixEnd_1706093 := by exact prefixLift 1706093
  have htrace : WordTrace (prefixWord ++ tailWord_1706093) baseStart_1706093 baseEnd_1706093 := by
    simpa [prefixWord, tailWord_1706093, baseEnd_1706093] using wordTrace_append hprefix tailTrace_1706093
  have hstable : (prefixWord ++ tailWord_1706093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706093).length < 2 ^ (prefixWord ++ tailWord_1706093).sum := by decide
  have hdescent : baseEnd_1706093 < baseStart_1706093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706097 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 1, 4]
def baseStart_1706097 : Nat := 118140960795 + 1706097 * 2 ^ 59
def prefixEnd_1706097 : Nat := 4983230072969 + 3 ^ 40 * 1706097 * 2
def baseEnd_1706097 : Nat := 292015934731305540447103

theorem tailTrace_1706097 : CollatzResearch.WordTrace tailWord_1706097 prefixEnd_1706097 292015934731305540447103 := by
  unfold tailWord_1706097
  simp only [CollatzResearch.WordTrace]
  refine ⟨62226469700109422014908545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41484313133406281343272363 62226469700109422014908545)
  ·
    refine ⟨46669852275082066511181409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62226469700109422014908545 46669852275082066511181409)
    ·
      refine ⟨35002389206311549883386057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46669852275082066511181409 35002389206311549883386057)
      ·
        refine ⟨26251791904733662412539543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35002389206311549883386057 26251791904733662412539543)
        ·
          refine ⟨39377687857100493618809315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26251791904733662412539543 39377687857100493618809315)
          ·
            refine ⟨59066531785650740428213973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39377687857100493618809315 59066531785650740428213973)
            ·
              refine ⟨1384371838726189228786265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59066531785650740428213973 1384371838726189228786265)
              ·
                refine ⟨1038278879044641921589699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384371838726189228786265 1038278879044641921589699)
                ·
                  refine ⟨1557418318566962882384549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038278879044641921589699 1557418318566962882384549)
                  ·
                    refine ⟨292015934731305540447103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557418318566962882384549 292015934731305540447103)
                    ·
                      rfl

theorem cell23_1706097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 4].length) (baseStart_1706097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706097 prefixEnd_1706097 := by exact prefixLift 1706097
  have htrace : WordTrace (prefixWord ++ tailWord_1706097) baseStart_1706097 baseEnd_1706097 := by
    simpa [prefixWord, tailWord_1706097, baseEnd_1706097] using wordTrace_append hprefix tailTrace_1706097
  have hstable : (prefixWord ++ tailWord_1706097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706097).length < 2 ^ (prefixWord ++ tailWord_1706097).sum := by decide
  have hdescent : baseEnd_1706097 < baseStart_1706097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706170 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 2, 4]
def baseStart_1706170 : Nat := 118140960795 + 1706170 * 2 ^ 59
def prefixEnd_1706170 : Nat := 4983230072969 + 3 ^ 40 * 1706170 * 2
def baseEnd_1706170 : Nat := 292028429427231611909491

theorem tailTrace_1706170 : CollatzResearch.WordTrace tailWord_1706170 prefixEnd_1706170 292028429427231611909491 := by
  unfold tailWord_1706170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557283057211238870578991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41486088152563303654877309 15557283057211238870578991)
  ·
    refine ⟨23335924585816858305868487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15557283057211238870578991 23335924585816858305868487)
    ·
      refine ⟨35003886878725287458802731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23335924585816858305868487 35003886878725287458802731)
      ·
        refine ⟨52505830318087931188204097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35003886878725287458802731 52505830318087931188204097)
        ·
          refine ⟨39379372738565948391153073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52505830318087931188204097 39379372738565948391153073)
          ·
            refine ⟨29534529553924461293364805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39379372738565948391153073 29534529553924461293364805)
            ·
              refine ⟨5537724291360836492505901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29534529553924461293364805 5537724291360836492505901)
              ·
                refine ⟨2076646609260313684689713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5537724291360836492505901 2076646609260313684689713)
                ·
                  refine ⟨1557484956945235263517285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2076646609260313684689713 1557484956945235263517285)
                  ·
                    refine ⟨292028429427231611909491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557484956945235263517285 292028429427231611909491)
                    ·
                      rfl

theorem cell23_1706170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_1706170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706170 prefixEnd_1706170 := by exact prefixLift 1706170
  have htrace : WordTrace (prefixWord ++ tailWord_1706170) baseStart_1706170 baseEnd_1706170 := by
    simpa [prefixWord, tailWord_1706170, baseEnd_1706170] using wordTrace_append hprefix tailTrace_1706170
  have hstable : (prefixWord ++ tailWord_1706170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706170).length < 2 ^ (prefixWord ++ tailWord_1706170).sum := by decide
  have hdescent : baseEnd_1706170 < baseStart_1706170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706190 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1706190 : Nat := 118140960795 + 1706190 * 2 ^ 59
def prefixEnd_1706190 : Nat := 4983230072969 + 3 ^ 40 * 1706190 * 2
def baseEnd_1706190 : Nat := 876095557894784757478381

theorem tailTrace_1706190 : CollatzResearch.WordTrace tailWord_1706190 prefixEnd_1706190 876095557894784757478381 := by
  unfold tailWord_1706190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778732711096562362255503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41486574459181665932029349 7778732711096562362255503)
  ·
    refine ⟨11668099066644843543383255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778732711096562362255503 11668099066644843543383255)
    ·
      refine ⟨17502148599967265315074883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668099066644843543383255 17502148599967265315074883)
      ·
        refine ⟨26253222899950897972612325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17502148599967265315074883 26253222899950897972612325)
        ·
          refine ⟨4922479293740793369864811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26253222899950897972612325 4922479293740793369864811)
          ·
            refine ⟨7383718940611190054797217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922479293740793369864811 7383718940611190054797217)
            ·
              refine ⟨5537789205458392541097913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7383718940611190054797217 5537789205458392541097913)
              ·
                refine ⟨4153341904093794405823435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537789205458392541097913 4153341904093794405823435)
                ·
                  refine ⟨6230012856140691608735153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153341904093794405823435 6230012856140691608735153)
                  ·
                    refine ⟨4672509642105518706551365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6230012856140691608735153 4672509642105518706551365)
                    ·
                      refine ⟨876095557894784757478381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4672509642105518706551365 876095557894784757478381)
                      ·
                        rfl

theorem cell23_1706190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1706190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706190 prefixEnd_1706190 := by exact prefixLift 1706190
  have htrace : WordTrace (prefixWord ++ tailWord_1706190) baseStart_1706190 baseEnd_1706190 := by
    simpa [prefixWord, tailWord_1706190, baseEnd_1706190] using wordTrace_append hprefix tailTrace_1706190
  have hstable : (prefixWord ++ tailWord_1706190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706190).length < 2 ^ (prefixWord ++ tailWord_1706190).sum := by decide
  have hdescent : baseEnd_1706190 < baseStart_1706190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706194 : List Nat := [3, 2, 2, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_1706194 : Nat := 118140960795 + 1706194 * 2 ^ 59
def prefixEnd_1706194 : Nat := 4983230072969 + 3 ^ 40 * 1706194 * 2
def baseEnd_1706194 : Nat := 876097611817402741828363

theorem tailTrace_1706194 : CollatzResearch.WordTrace tailWord_1706194 prefixEnd_1706194 876097611817402741828363 := by
  unfold tailWord_1706194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557501895189501895297409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41486671720505338387459757 15557501895189501895297409)
  ·
    refine ⟨11668126421392126421473057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15557501895189501895297409 11668126421392126421473057)
    ·
      refine ⟨8751094816044094816104793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11668126421392126421473057 8751094816044094816104793)
      ·
        refine ⟨6563321112033071112078595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8751094816044094816104793 6563321112033071112078595)
        ·
          refine ⟨9844981668049606668117893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563321112033071112078595 9844981668049606668117893)
          ·
            refine ⟨1845934062759301250272105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9844981668049606668117893 1845934062759301250272105)
            ·
              refine ⟨1384450547069475937704079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1845934062759301250272105 1384450547069475937704079)
              ·
                refine ⟨2076675820604213906556119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1384450547069475937704079 2076675820604213906556119)
                ·
                  refine ⟨3115013730906320859834179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076675820604213906556119 3115013730906320859834179)
                  ·
                    refine ⟨4672520596359481289751269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3115013730906320859834179 4672520596359481289751269)
                    ·
                      refine ⟨876097611817402741828363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4672520596359481289751269 876097611817402741828363)
                      ·
                        rfl

theorem cell23_1706194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_1706194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706194 prefixEnd_1706194 := by exact prefixLift 1706194
  have htrace : WordTrace (prefixWord ++ tailWord_1706194) baseStart_1706194 baseEnd_1706194 := by
    simpa [prefixWord, tailWord_1706194, baseEnd_1706194] using wordTrace_append hprefix tailTrace_1706194
  have hstable : (prefixWord ++ tailWord_1706194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706194).length < 2 ^ (prefixWord ++ tailWord_1706194).sum := by decide
  have hdescent : baseEnd_1706194 < baseStart_1706194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706204 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1706204 : Nat := 118140960795 + 1706204 * 2 ^ 59
def prefixEnd_1706204 : Nat := 4983230072969 + 3 ^ 40 * 1706204 * 2
def baseEnd_1706204 : Nat := 292034248874649234234439

theorem tailTrace_1706204 : CollatzResearch.WordTrace tailWord_1706204 prefixEnd_1706204 292034248874649234234439 := by
  unfold tailWord_1706204
  simp only [CollatzResearch.WordTrace]
  refine ⟨31115186155360889644526833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41486914873814519526035777 31115186155360889644526833)
  ·
    refine ⟨23336389616520667233395125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31115186155360889644526833 23336389616520667233395125)
    ·
      refine ⟨2187786526548812553130793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23336389616520667233395125 2187786526548812553130793)
      ·
        refine ⟨1640839894911609414848095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2187786526548812553130793 1640839894911609414848095)
        ·
          refine ⟨2461259842367414122272143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640839894911609414848095 2461259842367414122272143)
          ·
            refine ⟨3691889763551121183408215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461259842367414122272143 3691889763551121183408215)
            ·
              refine ⟨5537834645326681775112323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691889763551121183408215 5537834645326681775112323)
              ·
                refine ⟨8306751967990022662668485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537834645326681775112323 8306751967990022662668485)
                ·
                  refine ⟨1557515993998129249250341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8306751967990022662668485 1557515993998129249250341)
                  ·
                    refine ⟨292034248874649234234439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1557515993998129249250341 292034248874649234234439)
                    ·
                      rfl

theorem cell23_1706204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1706204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706204 prefixEnd_1706204 := by exact prefixLift 1706204
  have htrace : WordTrace (prefixWord ++ tailWord_1706204) baseStart_1706204 baseEnd_1706204 := by
    simpa [prefixWord, tailWord_1706204, baseEnd_1706204] using wordTrace_append hprefix tailTrace_1706204
  have hstable : (prefixWord ++ tailWord_1706204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706204).length < 2 ^ (prefixWord ++ tailWord_1706204).sum := by decide
  have hdescent : baseEnd_1706204 < baseStart_1706204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706211 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1706211 : Nat := 118140960795 + 1706211 * 2 ^ 59
def prefixEnd_1706211 : Nat := 4983230072969 + 3 ^ 40 * 1706211 * 2
def baseEnd_1706211 : Nat := 876106340988529175315785

theorem tailTrace_1706211 : CollatzResearch.WordTrace tailWord_1706211 prefixEnd_1706211 876106340988529175315785 := by
  unfold tailWord_1706211
  simp only [CollatzResearch.WordTrace]
  refine ⟨62230627621696419484558487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41487085081130946323038991 62230627621696419484558487)
  ·
    refine ⟨93345941432544629226837731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62230627621696419484558487 93345941432544629226837731)
    ·
      refine ⟨140018912148816943840256597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93345941432544629226837731 140018912148816943840256597)
      ·
        refine ⟨1640846626743948560628007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 140018912148816943840256597 1640846626743948560628007)
        ·
          refine ⟨2461269940115922840942011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1640846626743948560628007 2461269940115922840942011)
          ·
            refine ⟨3691904910173884261413017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461269940115922840942011 3691904910173884261413017)
            ·
              refine ⟨2768928682630413196059763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691904910173884261413017 2768928682630413196059763)
              ·
                refine ⟨4153393023945619794089645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768928682630413196059763 4153393023945619794089645)
                ·
                  refine ⟨1557522383979607422783617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4153393023945619794089645 1557522383979607422783617)
                  ·
                    refine ⟨1168141787984705567087713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557522383979607422783617 1168141787984705567087713)
                    ·
                      refine ⟨876106340988529175315785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168141787984705567087713 876106340988529175315785)
                      ·
                        rfl

theorem cell23_1706211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1706211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706211 prefixEnd_1706211 := by exact prefixLift 1706211
  have htrace : WordTrace (prefixWord ++ tailWord_1706211) baseStart_1706211 baseEnd_1706211 := by
    simpa [prefixWord, tailWord_1706211, baseEnd_1706211] using wordTrace_append hprefix tailTrace_1706211
  have hstable : (prefixWord ++ tailWord_1706211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706211).length < 2 ^ (prefixWord ++ tailWord_1706211).sum := by decide
  have hdescent : baseEnd_1706211 < baseStart_1706211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706267 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 4, 2, 2]
def baseStart_1706267 : Nat := 118140960795 + 1706267 * 2 ^ 59
def prefixEnd_1706267 : Nat := 4983230072969 + 3 ^ 40 * 1706267 * 2
def baseEnd_1706267 : Nat := 876135095905180956215527

theorem tailTrace_1706267 : CollatzResearch.WordTrace tailWord_1706267 prefixEnd_1706267 876135095905180956215527 := by
  unfold tailWord_1706267
  simp only [CollatzResearch.WordTrace]
  refine ⟨62232670109493541048597055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41488446739662360699064703 62232670109493541048597055)
  ·
    refine ⟨93349005164240311572895583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62232670109493541048597055 93349005164240311572895583)
    ·
      refine ⟨140023507746360467359343375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93349005164240311572895583 140023507746360467359343375)
      ·
        refine ⟨210035261619540701039015063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140023507746360467359343375 210035261619540701039015063)
        ·
          refine ⟨315052892429311051558522595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210035261619540701039015063 315052892429311051558522595)
          ·
            refine ⟨472579338643966577337783893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315052892429311051558522595 472579338643966577337783893)
            ·
              refine ⟨5538039124733983328177155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 472579338643966577337783893 5538039124733983328177155)
              ·
                refine ⟨8307058687100974992265733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538039124733983328177155 8307058687100974992265733)
                ·
                  refine ⟨1557573503831432811049825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8307058687100974992265733 1557573503831432811049825)
                  ·
                    refine ⟨1168180127873574608287369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557573503831432811049825 1168180127873574608287369)
                    ·
                      refine ⟨876135095905180956215527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168180127873574608287369 876135095905180956215527)
                      ·
                        rfl

theorem cell23_1706267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 2, 2].length) (baseStart_1706267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706267 prefixEnd_1706267 := by exact prefixLift 1706267
  have htrace : WordTrace (prefixWord ++ tailWord_1706267) baseStart_1706267 baseEnd_1706267 := by
    simpa [prefixWord, tailWord_1706267, baseEnd_1706267] using wordTrace_append hprefix tailTrace_1706267
  have hstable : (prefixWord ++ tailWord_1706267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706267).length < 2 ^ (prefixWord ++ tailWord_1706267).sum := by decide
  have hdescent : baseEnd_1706267 < baseStart_1706267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706320 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_1706320 : Nat := 118140960795 + 1706320 * 2 ^ 59
def prefixEnd_1706320 : Nat := 4983230072969 + 3 ^ 40 * 1706320 * 2
def baseEnd_1706320 : Nat := 292054103459956416284261

theorem tailTrace_1706320 : CollatzResearch.WordTrace tailWord_1706320 prefixEnd_1706320 292054103459956416284261 := by
  unfold tailWord_1706320
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117301589150765550138207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41489735452201020733517609 31117301589150765550138207)
  ·
    refine ⟨46675952383726148325207311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31117301589150765550138207 46675952383726148325207311)
    ·
      refine ⟨70013928575589222487810967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46675952383726148325207311 70013928575589222487810967)
      ·
        refine ⟨105020892863383833731716451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70013928575589222487810967 105020892863383833731716451)
        ·
          refine ⟨157531339295075750597574677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105020892863383833731716451 157531339295075750597574677)
          ·
            refine ⟨7384281529456675809261313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157531339295075750597574677 7384281529456675809261313)
            ·
              refine ⟨5538211147092506856945985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7384281529456675809261313 5538211147092506856945985)
              ·
                refine ⟨4153658360319380142709489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5538211147092506856945985 4153658360319380142709489)
                ·
                  refine ⟨3115243770239535107032117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153658360319380142709489 3115243770239535107032117)
                  ·
                    refine ⟨292054103459956416284261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3115243770239535107032117 292054103459956416284261)
                    ·
                      rfl

theorem cell23_1706320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_1706320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706320 prefixEnd_1706320 := by exact prefixLift 1706320
  have htrace : WordTrace (prefixWord ++ tailWord_1706320) baseStart_1706320 baseEnd_1706320 := by
    simpa [prefixWord, tailWord_1706320, baseEnd_1706320] using wordTrace_append hprefix tailTrace_1706320
  have hstable : (prefixWord ++ tailWord_1706320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706320).length < 2 ^ (prefixWord ++ tailWord_1706320).sum := by decide
  have hdescent : baseEnd_1706320 < baseStart_1706320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706324 : List Nat := [2, 4, 1, 1, 2, 2, 4, 2, 5]
def baseStart_1706324 : Nat := 118140960795 + 1706324 * 2 ^ 59
def prefixEnd_1706324 : Nat := 4983230072969 + 3 ^ 40 * 1706324 * 2
def baseEnd_1706324 : Nat := 97351596033609692578085

theorem tailTrace_1706324 : CollatzResearch.WordTrace tailWord_1706324 prefixEnd_1706324 97351596033609692578085 := by
  unfold tailWord_1706324
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117374535143519891711013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41489832713524693188948017 31117374535143519891711013)
  ·
    refine ⟨5834507725339409979695815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31117374535143519891711013 5834507725339409979695815)
    ·
      refine ⟨8751761588009114969543723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5834507725339409979695815 8751761588009114969543723)
      ·
        refine ⟨13127642382013672454315585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751761588009114969543723 13127642382013672454315585)
        ·
          refine ⟨9845731786510254340736689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13127642382013672454315585 9845731786510254340736689)
          ·
            refine ⟨7384298839882690755552517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9845731786510254340736689 7384298839882690755552517)
            ·
              refine ⟨1384556032478004516666097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7384298839882690755552517 1384556032478004516666097)
              ·
                refine ⟨1038417024358503387499573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384556032478004516666097 1038417024358503387499573)
                ·
                  refine ⟨97351596033609692578085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038417024358503387499573 97351596033609692578085)
                  ·
                    rfl

theorem cell23_1706324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_1706324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706324 prefixEnd_1706324 := by exact prefixLift 1706324
  have htrace : WordTrace (prefixWord ++ tailWord_1706324) baseStart_1706324 baseEnd_1706324 := by
    simpa [prefixWord, tailWord_1706324, baseEnd_1706324] using wordTrace_append hprefix tailTrace_1706324
  have hstable : (prefixWord ++ tailWord_1706324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706324).length < 2 ^ (prefixWord ++ tailWord_1706324).sum := by decide
  have hdescent : baseEnd_1706324 < baseStart_1706324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706340 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1706340 : Nat := 118140960795 + 1706340 * 2 ^ 59
def prefixEnd_1706340 : Nat := 4983230072969 + 3 ^ 40 * 1706340 * 2
def baseEnd_1706340 : Nat := 876172579992959170602691

theorem tailTrace_1706340 : CollatzResearch.WordTrace tailWord_1706340 prefixEnd_1706340 876172579992959170602691 := by
  unfold tailWord_1706340
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117666319114537258002237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41490221758819383010669649 31117666319114537258002237)
  ·
    refine ⟨11669124869667951471750839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31117666319114537258002237 11669124869667951471750839)
    ·
      refine ⟨17503687304501927207626259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669124869667951471750839 17503687304501927207626259)
      ·
        refine ⟨26255530956752890811439389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503687304501927207626259 26255530956752890811439389)
        ·
          refine ⟨9845824108782334054289771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26255530956752890811439389 9845824108782334054289771)
          ·
            refine ⟨14768736163173501081434657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845824108782334054289771 14768736163173501081434657)
            ·
              refine ⟨11076552122380125811075993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14768736163173501081434657 11076552122380125811075993)
              ·
                refine ⟨8307414091785094358306995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11076552122380125811075993 8307414091785094358306995)
                ·
                  refine ⟨12461121137677641537460493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8307414091785094358306995 12461121137677641537460493)
                  ·
                    refine ⟨4672920426629115576547685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12461121137677641537460493 4672920426629115576547685)
                    ·
                      refine ⟨876172579992959170602691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4672920426629115576547685 876172579992959170602691)
                      ·
                        rfl

theorem cell23_1706340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1706340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706340 prefixEnd_1706340 := by exact prefixLift 1706340
  have htrace : WordTrace (prefixWord ++ tailWord_1706340) baseStart_1706340 baseEnd_1706340 := by
    simpa [prefixWord, tailWord_1706340, baseEnd_1706340] using wordTrace_append hprefix tailTrace_1706340
  have hstable : (prefixWord ++ tailWord_1706340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706340).length < 2 ^ (prefixWord ++ tailWord_1706340).sum := by decide
  have hdescent : baseEnd_1706340 < baseStart_1706340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706357 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1706357 : Nat := 118140960795 + 1706357 * 2 ^ 59
def prefixEnd_1706357 : Nat := 4983230072969 + 3 ^ 40 * 1706357 * 2
def baseEnd_1706357 : Nat := 876181309164085604090113

theorem tailTrace_1706357 : CollatzResearch.WordTrace tailWord_1706357 prefixEnd_1706357 876181309164085604090113 := by
  unfold tailWord_1706357
  simp only [CollatzResearch.WordTrace]
  refine ⟨62235952679167486419373325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41490635119444990946248883 62235952679167486419373325)
  ·
    refine ⟨23338482254687807407264997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62235952679167486419373325 23338482254687807407264997)
    ·
      refine ⟨4375965422753963888862187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23338482254687807407264997 4375965422753963888862187)
      ·
        refine ⟨6563948134130945833293281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4375965422753963888862187 6563948134130945833293281)
        ·
          refine ⟨4922961100598209374969961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6563948134130945833293281 4922961100598209374969961)
          ·
            refine ⟨3692220825448657031227471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922961100598209374969961 3692220825448657031227471)
            ·
              refine ⟨5538331238172985546841207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692220825448657031227471 5538331238172985546841207)
              ·
                refine ⟨8307496857259478320261811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538331238172985546841207 8307496857259478320261811)
                ·
                  refine ⟨12461245285889217480392717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8307496857259478320261811 12461245285889217480392717)
                  ·
                    refine ⟨4672966982208456555147269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12461245285889217480392717 4672966982208456555147269)
                    ·
                      refine ⟨876181309164085604090113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4672966982208456555147269 876181309164085604090113)
                      ·
                        rfl

theorem cell23_1706357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1706357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706357 prefixEnd_1706357 := by exact prefixLift 1706357
  have htrace : WordTrace (prefixWord ++ tailWord_1706357) baseStart_1706357 baseEnd_1706357 := by
    simpa [prefixWord, tailWord_1706357, baseEnd_1706357] using wordTrace_append hprefix tailTrace_1706357
  have hstable : (prefixWord ++ tailWord_1706357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706357).length < 2 ^ (prefixWord ++ tailWord_1706357).sum := by decide
  have hdescent : baseEnd_1706357 < baseStart_1706357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706380 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 8]
def baseStart_1706380 : Nat := 118140960795 + 1706380 * 2 ^ 59
def prefixEnd_1706380 : Nat := 4983230072969 + 3 ^ 40 * 1706380 * 2
def baseEnd_1706380 : Nat := 97354791024348779344723

theorem tailTrace_1706380 : CollatzResearch.WordTrace tailWord_1706380 prefixEnd_1706380 97354791024348779344723 := by
  unfold tailWord_1706380
  simp only [CollatzResearch.WordTrace]
  refine ⟨31118395779042080673730297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41491194372056107564973729 31118395779042080673730297)
  ·
    refine ⟨23338796834281560505297723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31118395779042080673730297 23338796834281560505297723)
    ·
      refine ⟨35008195251422340757946585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23338796834281560505297723 35008195251422340757946585)
      ·
        refine ⟨26256146438566755568459939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35008195251422340757946585 26256146438566755568459939)
        ·
          refine ⟨39384219657850133352689909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26256146438566755568459939 39384219657850133352689909)
          ·
            refine ⟨3692270592923450001814679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39384219657850133352689909 3692270592923450001814679)
            ·
              refine ⟨5538405889385175002722019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692270592923450001814679 5538405889385175002722019)
              ·
                refine ⟨8307608834077762504083029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538405889385175002722019 8307608834077762504083029)
                ·
                  refine ⟨97354791024348779344723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8307608834077762504083029 97354791024348779344723)
                  ·
                    rfl

theorem cell23_1706380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_1706380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706380 prefixEnd_1706380 := by exact prefixLift 1706380
  have htrace : WordTrace (prefixWord ++ tailWord_1706380) baseStart_1706380 baseEnd_1706380 := by
    simpa [prefixWord, tailWord_1706380, baseEnd_1706380] using wordTrace_append hprefix tailTrace_1706380
  have hstable : (prefixWord ++ tailWord_1706380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706380).length < 2 ^ (prefixWord ++ tailWord_1706380).sum := by decide
  have hdescent : baseEnd_1706380 < baseStart_1706380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706464 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 5, 2, 2]
def baseStart_1706464 : Nat := 118140960795 + 1706464 * 2 ^ 59
def prefixEnd_1706464 : Nat := 4983230072969 + 3 ^ 40 * 1706464 * 2
def baseEnd_1706464 : Nat := 876236251594116685452121

theorem tailTrace_1706464 : CollatzResearch.WordTrace tailWord_1706464 prefixEnd_1706464 876236251594116685452121 := by
  unfold tailWord_1706464
  simp only [CollatzResearch.WordTrace]
  refine ⟨31119927644889921846759223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41493236859853229129012297 31119927644889921846759223)
  ·
    refine ⟨46679891467334882770138835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31119927644889921846759223 46679891467334882770138835)
    ·
      refine ⟨70019837201002324155208253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46679891467334882770138835 70019837201002324155208253)
      ·
        refine ⟨26257438950375871558203095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70019837201002324155208253 26257438950375871558203095)
        ·
          refine ⟨39386158425563807337304643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26257438950375871558203095 39386158425563807337304643)
          ·
            refine ⟨59079237638345711005956965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39386158425563807337304643 59079237638345711005956965)
            ·
              refine ⟨11077357057189820813616931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59079237638345711005956965 11077357057189820813616931)
              ·
                refine ⟨16616035585784731220425397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11077357057189820813616931 16616035585784731220425397)
                ·
                  refine ⟨1557753336167318551914881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16616035585784731220425397 1557753336167318551914881)
                  ·
                    refine ⟨1168315002125488913936161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557753336167318551914881 1168315002125488913936161)
                    ·
                      refine ⟨876236251594116685452121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168315002125488913936161 876236251594116685452121)
                      ·
                        rfl

theorem cell23_1706464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_1706464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706464 prefixEnd_1706464 := by exact prefixLift 1706464
  have htrace : WordTrace (prefixWord ++ tailWord_1706464) baseStart_1706464 baseEnd_1706464 := by
    simpa [prefixWord, tailWord_1706464, baseEnd_1706464] using wordTrace_append hprefix tailTrace_1706464
  have hstable : (prefixWord ++ tailWord_1706464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706464).length < 2 ^ (prefixWord ++ tailWord_1706464).sum := by decide
  have hdescent : baseEnd_1706464 < baseStart_1706464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706490 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1706490 : Nat := 118140960795 + 1706490 * 2 ^ 59
def prefixEnd_1706490 : Nat := 4983230072969 + 3 ^ 40 * 1706490 * 2
def baseEnd_1706490 : Nat := 876249602091133583727001

theorem tailTrace_1706490 : CollatzResearch.WordTrace tailWord_1706490 prefixEnd_1706490 876249602091133583727001 := by
  unfold tailWord_1706490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15560200896921412533491231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41493869058457100089309949 15560200896921412533491231)
  ·
    refine ⟨23340301345382118800236847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15560200896921412533491231 23340301345382118800236847)
    ·
      refine ⟨35010452018073178200355271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23340301345382118800236847 35010452018073178200355271)
      ·
        refine ⟨52515678027109767300532907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35010452018073178200355271 52515678027109767300532907)
        ·
          refine ⟨78773517040664650950799361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52515678027109767300532907 78773517040664650950799361)
          ·
            refine ⟨59080137780498488213099521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78773517040664650950799361 59080137780498488213099521)
            ·
              refine ⟨44310103335373866159824641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59080137780498488213099521 44310103335373866159824641)
              ·
                refine ⟨33232577501530399619868481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44310103335373866159824641 33232577501530399619868481)
                ·
                  refine ⟨24924433126147799714901361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33232577501530399619868481 24924433126147799714901361)
                  ·
                    refine ⟨18693324844610849786176021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24924433126147799714901361 18693324844610849786176021)
                    ·
                      refine ⟨876249602091133583727001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18693324844610849786176021 876249602091133583727001)
                      ·
                        rfl

theorem cell23_1706490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1706490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706490 prefixEnd_1706490 := by exact prefixLift 1706490
  have htrace : WordTrace (prefixWord ++ tailWord_1706490) baseStart_1706490 baseEnd_1706490 := by
    simpa [prefixWord, tailWord_1706490, baseEnd_1706490] using wordTrace_append hprefix tailTrace_1706490
  have hstable : (prefixWord ++ tailWord_1706490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706490).length < 2 ^ (prefixWord ++ tailWord_1706490).sum := by decide
  have hdescent : baseEnd_1706490 < baseStart_1706490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706532 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1706532 : Nat := 118140960795 + 1706532 * 2 ^ 59
def prefixEnd_1706532 : Nat := 4983230072969 + 3 ^ 40 * 1706532 * 2
def baseEnd_1706532 : Nat := 876271168278622419401809

theorem tailTrace_1706532 : CollatzResearch.WordTrace tailWord_1706532 prefixEnd_1706532 876271168278622419401809 := by
  unfold tailWord_1706532
  simp only [CollatzResearch.WordTrace]
  refine ⟨31121167726766745653496925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41494890302355660871329233 31121167726766745653496925)
  ·
    refine ⟨11670437897537529620061347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31121167726766745653496925 11670437897537529620061347)
    ·
      refine ⟨17505656846306294430092021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11670437897537529620061347 17505656846306294430092021)
      ·
        refine ⟨1641155329341215102821127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17505656846306294430092021 1641155329341215102821127)
        ·
          refine ⟨2461732994011822654231691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641155329341215102821127 2461732994011822654231691)
          ·
            refine ⟨3692599491017733981347537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461732994011822654231691 3692599491017733981347537)
            ·
              refine ⟨2769449618263300486010653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692599491017733981347537 2769449618263300486010653)
              ·
                refine ⟨1038543606848737682253995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2769449618263300486010653 1038543606848737682253995)
                ·
                  refine ⟨1557815410273106523380993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038543606848737682253995 1557815410273106523380993)
                  ·
                    refine ⟨1168361557704829892535745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557815410273106523380993 1168361557704829892535745)
                    ·
                      refine ⟨876271168278622419401809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168361557704829892535745 876271168278622419401809)
                      ·
                        rfl

theorem cell23_1706532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1706532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706532 prefixEnd_1706532 := by exact prefixLift 1706532
  have htrace : WordTrace (prefixWord ++ tailWord_1706532) baseStart_1706532 baseEnd_1706532 := by
    simpa [prefixWord, tailWord_1706532, baseEnd_1706532] using wordTrace_append hprefix tailTrace_1706532
  have hstable : (prefixWord ++ tailWord_1706532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706532).length < 2 ^ (prefixWord ++ tailWord_1706532).sum := by decide
  have hdescent : baseEnd_1706532 < baseStart_1706532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706571 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 2, 2, 2]
def baseStart_1706571 : Nat := 118140960795 + 1706571 * 2 ^ 59
def prefixEnd_1706571 : Nat := 4983230072969 + 3 ^ 40 * 1706571 * 2
def baseEnd_1706571 : Nat := 876291194024147766814129

theorem tailTrace_1706571 : CollatzResearch.WordTrace tailWord_1706571 prefixEnd_1706571 876291194024147766814129 := by
  unfold tailWord_1706571
  simp only [CollatzResearch.WordTrace]
  refine ⟨62243757900392200967663567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41495838600261467311775711 62243757900392200967663567)
  ·
    refine ⟨93365636850588301451495351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62243757900392200967663567 93365636850588301451495351)
    ·
      refine ⟨140048455275882452177243027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93365636850588301451495351 140048455275882452177243027)
      ·
        refine ⟨210072682913823678265864541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140048455275882452177243027 210072682913823678265864541)
        ·
          refine ⟨78777256092683879349699203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210072682913823678265864541 78777256092683879349699203)
          ·
            refine ⟨118165884139025819024548805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78777256092683879349699203 118165884139025819024548805)
            ·
              refine ⟨22156103276067341067102901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118165884139025819024548805 22156103276067341067102901)
              ·
                refine ⟨2077134682131313225040897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22156103276067341067102901 2077134682131313225040897)
                ·
                  refine ⟨1557851011598484918780673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2077134682131313225040897 1557851011598484918780673)
                  ·
                    refine ⟨1168388258698863689085505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1557851011598484918780673 1168388258698863689085505)
                    ·
                      refine ⟨876291194024147766814129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168388258698863689085505 876291194024147766814129)
                      ·
                        rfl

theorem cell23_1706571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 2, 2].length) (baseStart_1706571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706571 prefixEnd_1706571 := by exact prefixLift 1706571
  have htrace : WordTrace (prefixWord ++ tailWord_1706571) baseStart_1706571 baseEnd_1706571 := by
    simpa [prefixWord, tailWord_1706571, baseEnd_1706571] using wordTrace_append hprefix tailTrace_1706571
  have hstable : (prefixWord ++ tailWord_1706571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706571).length < 2 ^ (prefixWord ++ tailWord_1706571).sum := by decide
  have hdescent : baseEnd_1706571 < baseStart_1706571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706577 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 7]
def baseStart_1706577 : Nat := 118140960795 + 1706577 * 2 ^ 59
def prefixEnd_1706577 : Nat := 4983230072969 + 3 ^ 40 * 1706577 * 2
def baseEnd_1706577 : Nat := 97366030545341638148789

theorem tailTrace_1706577 : CollatzResearch.WordTrace tailWord_1706577 prefixEnd_1706577 97366030545341638148789 := by
  unfold tailWord_1706577
  simp only [CollatzResearch.WordTrace]
  refine ⟨62243976738370463992381985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41495984492246975994921323 62243976738370463992381985)
  ·
    refine ⟨46682982553777847994286489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62243976738370463992381985 46682982553777847994286489)
    ·
      refine ⟨35012236915333385995714867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46682982553777847994286489 35012236915333385995714867)
      ·
        refine ⟨52518355373000078993572301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35012236915333385995714867 52518355373000078993572301)
        ·
          refine ⟨19694383264875029622589613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52518355373000078993572301 19694383264875029622589613)
          ·
            refine ⟨7385393724328136108471105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19694383264875029622589613 7385393724328136108471105)
            ·
              refine ⟨5539045293246102081353329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385393724328136108471105 5539045293246102081353329)
              ·
                refine ⟨4154283969934576561014997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539045293246102081353329 4154283969934576561014997)
                ·
                  refine ⟨97366030545341638148789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4154283969934576561014997 97366030545341638148789)
                  ·
                    rfl

theorem cell23_1706577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 7].length) (baseStart_1706577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706577 prefixEnd_1706577 := by exact prefixLift 1706577
  have htrace : WordTrace (prefixWord ++ tailWord_1706577) baseStart_1706577 baseEnd_1706577 := by
    simpa [prefixWord, tailWord_1706577, baseEnd_1706577] using wordTrace_append hprefix tailTrace_1706577
  have hstable : (prefixWord ++ tailWord_1706577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706577).length < 2 ^ (prefixWord ++ tailWord_1706577).sum := by decide
  have hdescent : baseEnd_1706577 < baseStart_1706577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706607 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 4, 5]
def baseStart_1706607 : Nat := 118140960795 + 1706607 * 2 ^ 59
def prefixEnd_1706607 : Nat := 4983230072969 + 3 ^ 40 * 1706607 * 2
def baseEnd_1706607 : Nat := 292103226442569875321321

theorem tailTrace_1706607 : CollatzResearch.WordTrace tailWord_1706607 prefixEnd_1706607 292103226442569875321321 := by
  unfold tailWord_1706607
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245070928261779115974075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41496713952174519410649383 62245070928261779115974075)
  ·
    refine ⟨93367606392392668673961113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62245070928261779115974075 93367606392392668673961113)
    ·
      refine ⟨70025704794294501505470835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93367606392392668673961113 70025704794294501505470835)
      ·
        refine ⟨105038557191441752258206253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70025704794294501505470835 105038557191441752258206253)
        ·
          refine ⟨39389458946790657096827345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105038557191441752258206253 39389458946790657096827345)
          ·
            refine ⟨29542094210092992822620509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39389458946790657096827345 29542094210092992822620509)
            ·
              refine ⟨11078285328784872308482691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29542094210092992822620509 11078285328784872308482691)
              ·
                refine ⟨16617427993177308462724037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078285328784872308482691 16617427993177308462724037)
                ·
                  refine ⟨3115767748720745336760757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16617427993177308462724037 3115767748720745336760757)
                  ·
                    refine ⟨292103226442569875321321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3115767748720745336760757 292103226442569875321321)
                    ·
                      rfl

theorem cell23_1706607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_1706607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706607 prefixEnd_1706607 := by exact prefixLift 1706607
  have htrace : WordTrace (prefixWord ++ tailWord_1706607) baseStart_1706607 baseEnd_1706607 := by
    simpa [prefixWord, tailWord_1706607, baseEnd_1706607] using wordTrace_append hprefix tailTrace_1706607
  have hstable : (prefixWord ++ tailWord_1706607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706607).length < 2 ^ (prefixWord ++ tailWord_1706607).sum := by decide
  have hdescent : baseEnd_1706607 < baseStart_1706607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706617 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1706617 : Nat := 118140960795 + 1706617 * 2 ^ 59
def prefixEnd_1706617 : Nat := 4983230072969 + 3 ^ 40 * 1706617 * 2
def baseEnd_1706617 : Nat := 876314814134254586838917

theorem tailTrace_1706617 : CollatzResearch.WordTrace tailWord_1706617 prefixEnd_1706617 876314814134254586838917 := by
  unfold tailWord_1706617
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245435658225550823838105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41496957105483700549225403 62245435658225550823838105)
  ·
    refine ⟨46684076743669163117878579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62245435658225550823838105 46684076743669163117878579)
    ·
      refine ⟨70026115115503744676817869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46684076743669163117878579 70026115115503744676817869)
      ·
        refine ⟨26259793168313904253806701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70026115115503744676817869 26259793168313904253806701)
        ·
          refine ⟨9847422438117714095177513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26259793168313904253806701 9847422438117714095177513)
          ·
            refine ⟨7385566828588285571383135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9847422438117714095177513 7385566828588285571383135)
            ·
              refine ⟨11078350242882428357074703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385566828588285571383135 11078350242882428357074703)
              ·
                refine ⟨16617525364323642535612055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078350242882428357074703 16617525364323642535612055)
                ·
                  refine ⟨24926288046485463803418083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16617525364323642535612055 24926288046485463803418083)
                  ·
                    refine ⟨37389432069728195705127125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24926288046485463803418083 37389432069728195705127125)
                    ·
                      refine ⟨876314814134254586838917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37389432069728195705127125 876314814134254586838917)
                      ·
                        rfl

theorem cell23_1706617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1706617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706617 prefixEnd_1706617 := by exact prefixLift 1706617
  have htrace : WordTrace (prefixWord ++ tailWord_1706617) baseStart_1706617 baseEnd_1706617 := by
    simpa [prefixWord, tailWord_1706617, baseEnd_1706617] using wordTrace_append hprefix tailTrace_1706617
  have hstable : (prefixWord ++ tailWord_1706617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706617).length < 2 ^ (prefixWord ++ tailWord_1706617).sum := by decide
  have hdescent : baseEnd_1706617 < baseStart_1706617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706626 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1706626 : Nat := 118140960795 + 1706626 * 2 ^ 59
def prefixEnd_1706626 : Nat := 4983230072969 + 3 ^ 40 * 1706626 * 2
def baseEnd_1706626 : Nat := 876319435460145051626377

theorem tailTrace_1706626 : CollatzResearch.WordTrace tailWord_1706626 prefixEnd_1706626 876319435460145051626377 := by
  unfold tailWord_1706626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15561440978798236340228933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41497175943461963573943821 15561440978798236340228933)
  ·
    refine ⟨2917770183524669313792925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15561440978798236340228933 2917770183524669313792925)
    ·
      refine ⟨1094163818821750992672347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2917770183524669313792925 1094163818821750992672347)
      ·
        refine ⟨1641245728232626489008521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094163818821750992672347 1641245728232626489008521)
        ·
          refine ⟨1230934296174469866756391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641245728232626489008521 1230934296174469866756391)
          ·
            refine ⟨1846401444261704800134587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230934296174469866756391 1846401444261704800134587)
            ·
              refine ⟨2769602166392557200201881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846401444261704800134587 2769602166392557200201881)
              ·
                refine ⟨2077201624794417900151411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769602166392557200201881 2077201624794417900151411)
                ·
                  refine ⟨3115802437191626850227117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077201624794417900151411 3115802437191626850227117)
                  ·
                    refine ⟨1168425913946860068835169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115802437191626850227117 1168425913946860068835169)
                    ·
                      refine ⟨876319435460145051626377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168425913946860068835169 876319435460145051626377)
                      ·
                        rfl

theorem cell23_1706626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1706626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706626 prefixEnd_1706626 := by exact prefixLift 1706626
  have htrace : WordTrace (prefixWord ++ tailWord_1706626) baseStart_1706626 baseEnd_1706626 := by
    simpa [prefixWord, tailWord_1706626, baseEnd_1706626] using wordTrace_append hprefix tailTrace_1706626
  have hstable : (prefixWord ++ tailWord_1706626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706626).length < 2 ^ (prefixWord ++ tailWord_1706626).sum := by decide
  have hdescent : baseEnd_1706626 < baseStart_1706626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706627 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1706627 : Nat := 118140960795 + 1706627 * 2 ^ 59
def prefixEnd_1706627 : Nat := 4983230072969 + 3 ^ 40 * 1706627 * 2
def baseEnd_1706627 : Nat := 876319948940799547713871

theorem tailTrace_1706627 : CollatzResearch.WordTrace tailWord_1706627 prefixEnd_1706627 876319948940799547713871 := by
  unfold tailWord_1706627
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245800388189322531702135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41497200258792881687801423 62245800388189322531702135)
  ·
    refine ⟨93368700582283983797553203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62245800388189322531702135 93368700582283983797553203)
    ·
      refine ⟨140053050873425975696329805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93368700582283983797553203 140053050873425975696329805)
      ·
        refine ⟨52519894077534740886123677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140053050873425975696329805 52519894077534740886123677)
        ·
          refine ⟨19694960279075527832296379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52519894077534740886123677 19694960279075527832296379)
          ·
            refine ⟨29542440418613291748444569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19694960279075527832296379 29542440418613291748444569)
            ·
              refine ⟨22156830313959968811333427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29542440418613291748444569 22156830313959968811333427)
              ·
                refine ⟨33235245470939953217000141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22156830313959968811333427 33235245470939953217000141)
                ·
                  refine ⟨12463217051602482456375053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33235245470939953217000141 12463217051602482456375053)
                  ·
                    refine ⟨4673706394350930921140645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12463217051602482456375053 4673706394350930921140645)
                    ·
                      refine ⟨876319948940799547713871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4673706394350930921140645 876319948940799547713871)
                      ·
                        rfl

theorem cell23_1706627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1706627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706627 prefixEnd_1706627 := by exact prefixLift 1706627
  have htrace : WordTrace (prefixWord ++ tailWord_1706627) baseStart_1706627 baseEnd_1706627 := by
    simpa [prefixWord, tailWord_1706627, baseEnd_1706627] using wordTrace_append hprefix tailTrace_1706627
  have hstable : (prefixWord ++ tailWord_1706627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706627).length < 2 ^ (prefixWord ++ tailWord_1706627).sum := by decide
  have hdescent : baseEnd_1706627 < baseStart_1706627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706684 : List Nat := [2, 2, 2, 3, 1, 1, 1, 5, 6]
def baseStart_1706684 : Nat := 118140960795 + 1706684 * 2 ^ 59
def prefixEnd_1706684 : Nat := 4983230072969 + 3 ^ 40 * 1706684 * 2
def baseEnd_1706684 : Nat := 97372135259789536077901

theorem tailTrace_1706684 : CollatzResearch.WordTrace tailWord_1706684 prefixEnd_1706684 97372135259789536077901 := by
  unfold tailWord_1706684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31123939674491410633263553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41498586232655214177684737 31123939674491410633263553)
  ·
    refine ⟨23342954755868557974947665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31123939674491410633263553 23342954755868557974947665)
    ·
      refine ⟨17507216066901418481210749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23342954755868557974947665 17507216066901418481210749)
      ·
        refine ⟨6565206025088031930454031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17507216066901418481210749 6565206025088031930454031)
        ·
          refine ⟨9847809037632047895681047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565206025088031930454031 9847809037632047895681047)
          ·
            refine ⟨14771713556448071843521571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847809037632047895681047 14771713556448071843521571)
            ·
              refine ⟨22157570334672107765282357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14771713556448071843521571 22157570334672107765282357)
              ·
                refine ⟨2077272218875510102995221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22157570334672107765282357 2077272218875510102995221)
                ·
                  refine ⟨97372135259789536077901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2077272218875510102995221 97372135259789536077901)
                  ·
                    rfl

theorem cell23_1706684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_1706684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706684 prefixEnd_1706684 := by exact prefixLift 1706684
  have htrace : WordTrace (prefixWord ++ tailWord_1706684) baseStart_1706684 baseEnd_1706684 := by
    simpa [prefixWord, tailWord_1706684, baseEnd_1706684] using wordTrace_append hprefix tailTrace_1706684
  have hstable : (prefixWord ++ tailWord_1706684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706684).length < 2 ^ (prefixWord ++ tailWord_1706684).sum := by decide
  have hdescent : baseEnd_1706684 < baseStart_1706684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706698 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_1706698 : Nat := 118140960795 + 1706698 * 2 ^ 59
def prefixEnd_1706698 : Nat := 4983230072969 + 3 ^ 40 * 1706698 * 2
def baseEnd_1706698 : Nat := 876356406067268769926045

theorem tailTrace_1706698 : CollatzResearch.WordTrace tailWord_1706698 prefixEnd_1706698 876356406067268769926045 := by
  unfold tailWord_1706698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562097492733025414384187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41498926647288067771691165 15562097492733025414384187)
  ·
    refine ⟨23343146239099538121576281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15562097492733025414384187 23343146239099538121576281)
    ·
      refine ⟨17507359679324653591182211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23343146239099538121576281 17507359679324653591182211)
      ·
        refine ⟨26261039518986980386773317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17507359679324653591182211 26261039518986980386773317)
        ·
          refine ⟨4923944909810058822519997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26261039518986980386773317 4923944909810058822519997)
          ·
            refine ⟨1846479341178772058444999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4923944909810058822519997 1846479341178772058444999)
            ·
              refine ⟨2769719011768158087667499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846479341178772058444999 2769719011768158087667499)
              ·
                refine ⟨4154578517652237131501249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769719011768158087667499 4154578517652237131501249)
                ·
                  refine ⟨3115933888239177848625937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4154578517652237131501249 3115933888239177848625937)
                  ·
                    refine ⟨2336950416179383386469453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3115933888239177848625937 2336950416179383386469453)
                    ·
                      refine ⟨876356406067268769926045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2336950416179383386469453 876356406067268769926045)
                      ·
                        rfl

theorem cell23_1706698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_1706698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706698 prefixEnd_1706698 := by exact prefixLift 1706698
  have htrace : WordTrace (prefixWord ++ tailWord_1706698) baseStart_1706698 baseEnd_1706698 := by
    simpa [prefixWord, tailWord_1706698, baseEnd_1706698] using wordTrace_append hprefix tailTrace_1706698
  have hstable : (prefixWord ++ tailWord_1706698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706698).length < 2 ^ (prefixWord ++ tailWord_1706698).sum := by decide
  have hdescent : baseEnd_1706698 < baseStart_1706698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706764 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_1706764 : Nat := 118140960795 + 1706764 * 2 ^ 59
def prefixEnd_1706764 : Nat := 4983230072969 + 3 ^ 40 * 1706764 * 2
def baseEnd_1706764 : Nat := 876390295790465511700741

theorem tailTrace_1706764 : CollatzResearch.WordTrace tailWord_1706764 prefixEnd_1706764 876390295790465511700741 := by
  unfold tailWord_1706764
  simp only [CollatzResearch.WordTrace]
  refine ⟨31125398594346497464719673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41500531459128663286292897 31125398594346497464719673)
  ·
    refine ⟨23344048945759873098539755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31125398594346497464719673 23344048945759873098539755)
    ·
      refine ⟨35016073418639809647809633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23344048945759873098539755 35016073418639809647809633)
      ·
        refine ⟨26262055063979857235857225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35016073418639809647809633 26262055063979857235857225)
        ·
          refine ⟨19696541297984892926892919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26262055063979857235857225 19696541297984892926892919)
          ·
            refine ⟨29544811946977339390339379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19696541297984892926892919 29544811946977339390339379)
            ·
              refine ⟨44317217920466009085509069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29544811946977339390339379 44317217920466009085509069)
              ·
                refine ⟨16618956720174753407065901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44317217920466009085509069 16618956720174753407065901)
                ·
                  refine ⟨6232108770065532527649713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16618956720174753407065901 6232108770065532527649713)
                  ·
                    refine ⟨4674081577549149395737285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6232108770065532527649713 4674081577549149395737285)
                    ·
                      refine ⟨876390295790465511700741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4674081577549149395737285 876390295790465511700741)
                      ·
                        rfl

theorem cell23_1706764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_1706764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706764 prefixEnd_1706764 := by exact prefixLift 1706764
  have htrace : WordTrace (prefixWord ++ tailWord_1706764) baseStart_1706764 baseEnd_1706764 := by
    simpa [prefixWord, tailWord_1706764, baseEnd_1706764] using wordTrace_append hprefix tailTrace_1706764
  have hstable : (prefixWord ++ tailWord_1706764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706764).length < 2 ^ (prefixWord ++ tailWord_1706764).sum := by decide
  have hdescent : baseEnd_1706764 < baseStart_1706764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706771 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 3]
def baseStart_1706771 : Nat := 118140960795 + 1706771 * 2 ^ 59
def prefixEnd_1706771 : Nat := 4983230072969 + 3 ^ 40 * 1706771 * 2
def baseEnd_1706771 : Nat := 876393890155046984313209

theorem tailTrace_1706771 : CollatzResearch.WordTrace tailWord_1706771 prefixEnd_1706771 876393890155046984313209 := by
  unfold tailWord_1706771
  simp only [CollatzResearch.WordTrace]
  refine ⟨62251052499667635124944167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41500701666445090083296111 62251052499667635124944167)
  ·
    refine ⟨93376578749501452687416251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62251052499667635124944167 93376578749501452687416251)
    ·
      refine ⟨140064868124252179031124377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93376578749501452687416251 140064868124252179031124377)
      ·
        refine ⟨105048651093189134273343283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140064868124252179031124377 105048651093189134273343283)
        ·
          refine ⟨157572976639783701410014925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105048651093189134273343283 157572976639783701410014925)
          ·
            refine ⟨59089866239918888028755597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157572976639783701410014925 59089866239918888028755597)
            ·
              refine ⟨22158699839969583010783349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59089866239918888028755597 22158699839969583010783349)
              ·
                refine ⟨2077378109997148407260939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22158699839969583010783349 2077378109997148407260939)
                ·
                  refine ⟨3116067164995722610891409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077378109997148407260939 3116067164995722610891409)
                  ·
                    refine ⟨2337050373746791958168557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3116067164995722610891409 2337050373746791958168557)
                    ·
                      refine ⟨876393890155046984313209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337050373746791958168557 876393890155046984313209)
                      ·
                        rfl

theorem cell23_1706771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 1, 2, 3].length) (baseStart_1706771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706771 prefixEnd_1706771 := by exact prefixLift 1706771
  have htrace : WordTrace (prefixWord ++ tailWord_1706771) baseStart_1706771 baseEnd_1706771 := by
    simpa [prefixWord, tailWord_1706771, baseEnd_1706771] using wordTrace_append hprefix tailTrace_1706771
  have hstable : (prefixWord ++ tailWord_1706771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706771).length < 2 ^ (prefixWord ++ tailWord_1706771).sum := by decide
  have hdescent : baseEnd_1706771 < baseStart_1706771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706801 : List Nat := [1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 3]
def baseStart_1706801 : Nat := 118140960795 + 1706801 * 2 ^ 59
def prefixEnd_1706801 : Nat := 4983230072969 + 3 ^ 40 * 1706801 * 2
def baseEnd_1706801 : Nat := 876409294574681866938071

theorem tailTrace_1706801 : CollatzResearch.WordTrace tailWord_1706801 prefixEnd_1706801 876409294574681866938071 := by
  unfold tailWord_1706801
  simp only [CollatzResearch.WordTrace]
  refine ⟨62252146689558950248536257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41501431126372633499024171 62252146689558950248536257)
  ·
    refine ⟨46689110017169212686402193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62252146689558950248536257 46689110017169212686402193)
    ·
      refine ⟨35016832512876909514801645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46689110017169212686402193 35016832512876909514801645)
      ·
        refine ⟨13131312192328841068050617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35016832512876909514801645 13131312192328841068050617)
        ·
          refine ⟨9848484144246630801037963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13131312192328841068050617 9848484144246630801037963)
          ·
            refine ⟨14772726216369946201556945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9848484144246630801037963 14772726216369946201556945)
            ·
              refine ⟨11079544662277459651167709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14772726216369946201556945 11079544662277459651167709)
              ·
                refine ⟨4154829248354047369187891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11079544662277459651167709 4154829248354047369187891)
                ·
                  refine ⟨6232243872531071053781837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154829248354047369187891 6232243872531071053781837)
                  ·
                    refine ⟨2337091452199151645168189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6232243872531071053781837 2337091452199151645168189)
                    ·
                      refine ⟨876409294574681866938071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337091452199151645168189 876409294574681866938071)
                      ·
                        rfl

theorem cell23_1706801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_1706801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706801 prefixEnd_1706801 := by exact prefixLift 1706801
  have htrace : WordTrace (prefixWord ++ tailWord_1706801) baseStart_1706801 baseEnd_1706801 := by
    simpa [prefixWord, tailWord_1706801, baseEnd_1706801] using wordTrace_append hprefix tailTrace_1706801
  have hstable : (prefixWord ++ tailWord_1706801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706801).length < 2 ^ (prefixWord ++ tailWord_1706801).sum := by decide
  have hdescent : baseEnd_1706801 < baseStart_1706801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706805 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1706805 : Nat := 118140960795 + 1706805 * 2 ^ 59
def prefixEnd_1706805 : Nat := 4983230072969 + 3 ^ 40 * 1706805 * 2
def baseEnd_1706805 : Nat := 876411348497299851288053

theorem tailTrace_1706805 : CollatzResearch.WordTrace tailWord_1706805 prefixEnd_1706805 876411348497299851288053 := by
  unfold tailWord_1706805
  simp only [CollatzResearch.WordTrace]
  refine ⟨62252292581544458931681869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41501528387696305954454579 62252292581544458931681869)
  ·
    refine ⟨23344609718079172099380701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62252292581544458931681869 23344609718079172099380701)
    ·
      refine ⟨8754228644279689537267763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23344609718079172099380701 8754228644279689537267763)
      ·
        refine ⟨13131342966419534305901645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754228644279689537267763 13131342966419534305901645)
        ·
          refine ⟨4924253612407325364713117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13131342966419534305901645 4924253612407325364713117)
          ·
            refine ⟨1846595104652747011767419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4924253612407325364713117 1846595104652747011767419)
            ·
              refine ⟨2769892656979120517651129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846595104652747011767419 2769892656979120517651129)
              ·
                refine ⟨2077419492734340388238347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769892656979120517651129 2077419492734340388238347)
                ·
                  refine ⟨3116129239101510582357521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077419492734340388238347 3116129239101510582357521)
                  ·
                    refine ⟨2337096929326132936768141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3116129239101510582357521 2337096929326132936768141)
                    ·
                      refine ⟨876411348497299851288053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337096929326132936768141 876411348497299851288053)
                      ·
                        rfl

theorem cell23_1706805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1706805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706805 prefixEnd_1706805 := by exact prefixLift 1706805
  have htrace : WordTrace (prefixWord ++ tailWord_1706805) baseStart_1706805 baseEnd_1706805 := by
    simpa [prefixWord, tailWord_1706805, baseEnd_1706805] using wordTrace_append hprefix tailTrace_1706805
  have hstable : (prefixWord ++ tailWord_1706805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706805).length < 2 ^ (prefixWord ++ tailWord_1706805).sum := by decide
  have hdescent : baseEnd_1706805 < baseStart_1706805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706822 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1706822 : Nat := 118140960795 + 1706822 * 2 ^ 59
def prefixEnd_1706822 : Nat := 4983230072969 + 3 ^ 40 * 1706822 * 2
def baseEnd_1706822 : Nat := 876420077668426284775475

theorem tailTrace_1706822 : CollatzResearch.WordTrace tailWord_1706822 prefixEnd_1706822 876420077668426284775475 := by
  unfold tailWord_1706822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1945403519452589713595335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41501941748321913890033813 1945403519452589713595335)
  ·
    refine ⟨2918105279178884570393003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1945403519452589713595335 2918105279178884570393003)
    ·
      refine ⟨4377157918768326855589505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918105279178884570393003 4377157918768326855589505)
      ·
        refine ⟨3282868439076245141692129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4377157918768326855589505 3282868439076245141692129)
        ·
          refine ⟨2462151329307183856269097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3282868439076245141692129 2462151329307183856269097)
          ·
            refine ⟨1846613496980387892201823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462151329307183856269097 1846613496980387892201823)
            ·
              refine ⟨2769920245470581838302735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1846613496980387892201823 2769920245470581838302735)
              ·
                refine ⟨4154880368205872757454103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769920245470581838302735 4154880368205872757454103)
                ·
                  refine ⟨6232320552308809136181155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154880368205872757454103 6232320552308809136181155)
                  ·
                    refine ⟨9348480828463213704271733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232320552308809136181155 9348480828463213704271733)
                    ·
                      refine ⟨876420077668426284775475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9348480828463213704271733 876420077668426284775475)
                      ·
                        rfl

theorem cell23_1706822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1706822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706822 prefixEnd_1706822 := by exact prefixLift 1706822
  have htrace : WordTrace (prefixWord ++ tailWord_1706822) baseStart_1706822 baseEnd_1706822 := by
    simpa [prefixWord, tailWord_1706822, baseEnd_1706822] using wordTrace_append hprefix tailTrace_1706822
  have hstable : (prefixWord ++ tailWord_1706822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706822).length < 2 ^ (prefixWord ++ tailWord_1706822).sum := by decide
  have hdescent : baseEnd_1706822 < baseStart_1706822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706836 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_1706836 : Nat := 118140960795 + 1706836 * 2 ^ 59
def prefixEnd_1706836 : Nat := 4983230072969 + 3 ^ 40 * 1706836 * 2
def baseEnd_1706836 : Nat := 876427266397589230000411

theorem tailTrace_1706836 : CollatzResearch.WordTrace tailWord_1706836 prefixEnd_1706836 876427266397589230000411 := by
  unfold tailWord_1706836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31126711622216075613030181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41502282162954767484040241 31126711622216075613030181)
  ·
    refine ⟨5836258429165514177443159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31126711622216075613030181 5836258429165514177443159)
    ·
      refine ⟨8754387643748271266164739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836258429165514177443159 8754387643748271266164739)
      ·
        refine ⟨13131581465622406899247109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754387643748271266164739 13131581465622406899247109)
        ·
          refine ⟨2462171524804201293608833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13131581465622406899247109 2462171524804201293608833)
          ·
            refine ⟨1846628643603150970206625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462171524804201293608833 1846628643603150970206625)
            ·
              refine ⟨1384971482702363227654969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846628643603150970206625 1384971482702363227654969)
              ·
                refine ⟨1038728612026772420741227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1384971482702363227654969 1038728612026772420741227)
                ·
                  refine ⟨1558092918040158631111841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038728612026772420741227 1558092918040158631111841)
                  ·
                    refine ⟨1168569688530118973333881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558092918040158631111841 1168569688530118973333881)
                    ·
                      refine ⟨876427266397589230000411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168569688530118973333881 876427266397589230000411)
                      ·
                        rfl

theorem cell23_1706836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_1706836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706836 prefixEnd_1706836 := by exact prefixLift 1706836
  have htrace : WordTrace (prefixWord ++ tailWord_1706836) baseStart_1706836 baseEnd_1706836 := by
    simpa [prefixWord, tailWord_1706836, baseEnd_1706836] using wordTrace_append hprefix tailTrace_1706836
  have hstable : (prefixWord ++ tailWord_1706836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706836).length < 2 ^ (prefixWord ++ tailWord_1706836).sum := by decide
  have hdescent : baseEnd_1706836 < baseStart_1706836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706851 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 2, 6]
def baseStart_1706851 : Nat := 118140960795 + 1706851 * 2 ^ 59
def prefixEnd_1706851 : Nat := 4983230072969 + 3 ^ 40 * 1706851 * 2
def baseEnd_1706851 : Nat := 292144989535802223770947

theorem tailTrace_1706851 : CollatzResearch.WordTrace tailWord_1706851 prefixEnd_1706851 292144989535802223770947 := by
  unfold tailWord_1706851
  simp only [CollatzResearch.WordTrace]
  refine ⟨62253970339377808787856407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41502646892918539191904271 62253970339377808787856407)
  ·
    refine ⟨93380955509066713181784611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62253970339377808787856407 93380955509066713181784611)
    ·
      refine ⟨140071433263600069772676917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93380955509066713181784611 140071433263600069772676917)
      ·
        refine ⟨13131696868462506541188461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140071433263600069772676917 13131696868462506541188461)
        ·
          refine ⟨4924386325673439952945673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13131696868462506541188461 4924386325673439952945673)
          ·
            refine ⟨3693289744255079964709255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924386325673439952945673 3693289744255079964709255)
            ·
              refine ⟨5539934616382619947063883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693289744255079964709255 5539934616382619947063883)
              ·
                refine ⟨8309901924573929920595825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539934616382619947063883 8309901924573929920595825)
                ·
                  refine ⟨6232426443430447440446869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8309901924573929920595825 6232426443430447440446869)
                  ·
                    refine ⟨292144989535802223770947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6232426443430447440446869 292144989535802223770947)
                    ·
                      rfl

theorem cell23_1706851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 6].length) (baseStart_1706851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706851 prefixEnd_1706851 := by exact prefixLift 1706851
  have htrace : WordTrace (prefixWord ++ tailWord_1706851) baseStart_1706851 baseEnd_1706851 := by
    simpa [prefixWord, tailWord_1706851, baseEnd_1706851] using wordTrace_append hprefix tailTrace_1706851
  have hstable : (prefixWord ++ tailWord_1706851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706851).length < 2 ^ (prefixWord ++ tailWord_1706851).sum := by decide
  have hdescent : baseEnd_1706851 < baseStart_1706851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706861 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1706861 : Nat := 118140960795 + 1706861 * 2 ^ 59
def prefixEnd_1706861 : Nat := 4983230072969 + 3 ^ 40 * 1706861 * 2
def baseEnd_1706861 : Nat := 876440103413951632187795

theorem tailTrace_1706861 : CollatzResearch.WordTrace tailWord_1706861 prefixEnd_1706861 876440103413951632187795 := by
  unfold tailWord_1706861
  simp only [CollatzResearch.WordTrace]
  refine ⟨62254335069341580495720437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41502890046227720330480291 62254335069341580495720437)
  ·
    refine ⟨5836343912750773171473791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62254335069341580495720437 5836343912750773171473791)
    ·
      refine ⟨8754515869126159757210687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836343912750773171473791 8754515869126159757210687)
      ·
        refine ⟨13131773803689239635816031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754515869126159757210687 13131773803689239635816031)
        ·
          refine ⟨19697660705533859453724047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13131773803689239635816031 19697660705533859453724047)
          ·
            refine ⟨29546491058300789180586071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19697660705533859453724047 29546491058300789180586071)
            ·
              refine ⟨44319736587451183770879107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29546491058300789180586071 44319736587451183770879107)
              ·
                refine ⟨66479604881176775656318661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44319736587451183770879107 66479604881176775656318661)
                ·
                  refine ⟨12464925915220645435559749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66479604881176775656318661 12464925915220645435559749)
                  ·
                    refine ⟨2337173609103871019167453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12464925915220645435559749 2337173609103871019167453)
                    ·
                      refine ⟨876440103413951632187795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337173609103871019167453 876440103413951632187795)
                      ·
                        rfl

theorem cell23_1706861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1706861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706861 prefixEnd_1706861 := by exact prefixLift 1706861
  have htrace : WordTrace (prefixWord ++ tailWord_1706861) baseStart_1706861 baseEnd_1706861 := by
    simpa [prefixWord, tailWord_1706861, baseEnd_1706861] using wordTrace_append hprefix tailTrace_1706861
  have hstable : (prefixWord ++ tailWord_1706861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706861).length < 2 ^ (prefixWord ++ tailWord_1706861).sum := by decide
  have hdescent : baseEnd_1706861 < baseStart_1706861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706864 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 9]
def baseStart_1706864 : Nat := 118140960795 + 1706864 * 2 ^ 59
def prefixEnd_1706864 : Nat := 4983230072969 + 3 ^ 40 * 1706864 * 2
def baseEnd_1706864 : Nat := 97382404872879457827809

theorem tailTrace_1706864 : CollatzResearch.WordTrace tailWord_1706864 prefixEnd_1706864 97382404872879457827809 := by
  unfold tailWord_1706864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31127222244165356004039823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41502962992220474672053097 31127222244165356004039823)
  ·
    refine ⟨46690833366248034006059735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31127222244165356004039823 46690833366248034006059735)
    ·
      refine ⟨70036250049372051009089603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46690833366248034006059735 70036250049372051009089603)
      ·
        refine ⟨105054375074058076513634405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70036250049372051009089603 105054375074058076513634405)
        ·
          refine ⟨19697695326385889346306451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105054375074058076513634405 19697695326385889346306451)
          ·
            refine ⟨29546542989578834019459677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19697695326385889346306451 29546542989578834019459677)
            ·
              refine ⟨11079953621092062757297379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29546542989578834019459677 11079953621092062757297379)
              ·
                refine ⟨16619930431638094135946069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11079953621092062757297379 16619930431638094135946069)
                ·
                  refine ⟨97382404872879457827809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16619930431638094135946069 97382404872879457827809)
                  ·
                    rfl

theorem cell23_1706864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_1706864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706864 prefixEnd_1706864 := by exact prefixLift 1706864
  have htrace : WordTrace (prefixWord ++ tailWord_1706864) baseStart_1706864 baseEnd_1706864 := by
    simpa [prefixWord, tailWord_1706864, baseEnd_1706864] using wordTrace_append hprefix tailTrace_1706864
  have hstable : (prefixWord ++ tailWord_1706864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706864).length < 2 ^ (prefixWord ++ tailWord_1706864).sum := by decide
  have hdescent : baseEnd_1706864 < baseStart_1706864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706874 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_1706874 : Nat := 118140960795 + 1706874 * 2 ^ 59
def prefixEnd_1706874 : Nat := 4983230072969 + 3 ^ 40 * 1706874 * 2
def baseEnd_1706874 : Nat := 876446778662460081325235

theorem tailTrace_1706874 : CollatzResearch.WordTrace tailWord_1706874 prefixEnd_1706874 876446778662460081325235 := by
  unfold tailWord_1706874
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563702304573620928985919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41503206145529655810629117 15563702304573620928985919)
  ·
    refine ⟨23345553456860431393478879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15563702304573620928985919 23345553456860431393478879)
    ·
      refine ⟨35018330185290647090218319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23345553456860431393478879 35018330185290647090218319)
      ·
        refine ⟨52527495277935970635327479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35018330185290647090218319 52527495277935970635327479)
        ·
          refine ⟨78791242916903955952991219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52527495277935970635327479 78791242916903955952991219)
          ·
            refine ⟨118186864375355933929486829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78791242916903955952991219 118186864375355933929486829)
            ·
              refine ⟨44320074140758475223557561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118186864375355933929486829 44320074140758475223557561)
              ·
                refine ⟨33240055605568856417668171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44320074140758475223557561 33240055605568856417668171)
                ·
                  refine ⟨49860083408353284626502257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33240055605568856417668171 49860083408353284626502257)
                  ·
                    refine ⟨37395062556264963469876693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49860083408353284626502257 37395062556264963469876693)
                    ·
                      refine ⟨876446778662460081325235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37395062556264963469876693 876446778662460081325235)
                      ·
                        rfl

theorem cell23_1706874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_1706874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706874 prefixEnd_1706874 := by exact prefixLift 1706874
  have htrace : WordTrace (prefixWord ++ tailWord_1706874) baseStart_1706874 baseEnd_1706874 := by
    simpa [prefixWord, tailWord_1706874, baseEnd_1706874] using wordTrace_append hprefix tailTrace_1706874
  have hstable : (prefixWord ++ tailWord_1706874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706874).length < 2 ^ (prefixWord ++ tailWord_1706874).sum := by decide
  have hdescent : baseEnd_1706874 < baseStart_1706874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706891 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 3]
def baseStart_1706891 : Nat := 118140960795 + 1706891 * 2 ^ 59
def prefixEnd_1706891 : Nat := 4983230072969 + 3 ^ 40 * 1706891 * 2
def baseEnd_1706891 : Nat := 876455507833586514812657

theorem tailTrace_1706891 : CollatzResearch.WordTrace tailWord_1706891 prefixEnd_1706891 876455507833586514812657 := by
  unfold tailWord_1706891
  simp only [CollatzResearch.WordTrace]
  refine ⟨62255429259232895619312527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41503619506155263746208351 62255429259232895619312527)
  ·
    refine ⟨93383143888849343428968791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62255429259232895619312527 93383143888849343428968791)
    ·
      refine ⟨140074715833274015143453187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93383143888849343428968791 140074715833274015143453187)
      ·
        refine ⟨210112073749911022715179781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140074715833274015143453187 210112073749911022715179781)
        ·
          refine ⟨39396013828108316759096209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210112073749911022715179781 39396013828108316759096209)
          ·
            refine ⟨29547010371081237569322157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39396013828108316759096209 29547010371081237569322157)
            ·
              refine ⟨11080128889155464088495809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29547010371081237569322157 11080128889155464088495809)
              ·
                refine ⟨8310096666866598066371857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11080128889155464088495809 8310096666866598066371857)
                ·
                  refine ⟨6232572500149948549778893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8310096666866598066371857 6232572500149948549778893)
                  ·
                    refine ⟨2337214687556230706167085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6232572500149948549778893 2337214687556230706167085)
                    ·
                      refine ⟨876455507833586514812657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337214687556230706167085 876455507833586514812657)
                      ·
                        rfl

theorem cell23_1706891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 3].length) (baseStart_1706891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706891 prefixEnd_1706891 := by exact prefixLift 1706891
  have htrace : WordTrace (prefixWord ++ tailWord_1706891) baseStart_1706891 baseEnd_1706891 := by
    simpa [prefixWord, tailWord_1706891, baseEnd_1706891] using wordTrace_append hprefix tailTrace_1706891
  have hstable : (prefixWord ++ tailWord_1706891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706891).length < 2 ^ (prefixWord ++ tailWord_1706891).sum := by decide
  have hdescent : baseEnd_1706891 < baseStart_1706891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706911 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 1, 7]
def baseStart_1706911 : Nat := 118140960795 + 1706911 * 2 ^ 59
def prefixEnd_1706911 : Nat := 4983230072969 + 3 ^ 40 * 1706911 * 2
def baseEnd_1706911 : Nat := 292155259148892145520855

theorem tailTrace_1706911 : CollatzResearch.WordTrace tailWord_1706911 prefixEnd_1706911 292155259148892145520855 := by
  unfold tailWord_1706911
  simp only [CollatzResearch.WordTrace]
  refine ⟨62256158719160439035040587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41504105812773626023360391 62256158719160439035040587)
  ·
    refine ⟨93384238078740658552560881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62256158719160439035040587 93384238078740658552560881)
    ·
      refine ⟨70038178559055493914420661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93384238078740658552560881 70038178559055493914420661)
      ·
        refine ⟨6566079239911452554476937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70038178559055493914420661 6566079239911452554476937)
        ·
          refine ⟨4924559429933589415857703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6566079239911452554476937 4924559429933589415857703)
          ·
            refine ⟨7386839144900384123786555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924559429933589415857703 7386839144900384123786555)
            ·
              refine ⟨11080258717350576185679833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386839144900384123786555 11080258717350576185679833)
              ·
                refine ⟨8310194038012932139259875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11080258717350576185679833 8310194038012932139259875)
                ·
                  refine ⟨12465291057019398208889813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8310194038012932139259875 12465291057019398208889813)
                  ·
                    refine ⟨292155259148892145520855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12465291057019398208889813 292155259148892145520855)
                    ·
                      rfl

theorem cell23_1706911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_1706911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706911 prefixEnd_1706911 := by exact prefixLift 1706911
  have htrace : WordTrace (prefixWord ++ tailWord_1706911) baseStart_1706911 baseEnd_1706911 := by
    simpa [prefixWord, tailWord_1706911, baseEnd_1706911] using wordTrace_append hprefix tailTrace_1706911
  have hstable : (prefixWord ++ tailWord_1706911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706911).length < 2 ^ (prefixWord ++ tailWord_1706911).sum := by decide
  have hdescent : baseEnd_1706911 < baseStart_1706911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1706932 : List Nat := [2, 5, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1706932 : Nat := 118140960795 + 1706932 * 2 ^ 59
def prefixEnd_1706932 : Nat := 4983230072969 + 3 ^ 40 * 1706932 * 2
def baseEnd_1706932 : Nat := 97386284504491206044441

theorem tailTrace_1706932 : CollatzResearch.WordTrace tailWord_1706932 prefixEnd_1706932 97386284504491206044441 := by
  unfold tailWord_1706932
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128462326042179810777525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41504616434722906414370033 31128462326042179810777525)
  ·
    refine ⟨2918293343066454357260393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31128462326042179810777525 2918293343066454357260393)
    ·
      refine ⟨2188720007299840767945295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2918293343066454357260393 2188720007299840767945295)
      ·
        refine ⟨3283080010949761151917943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188720007299840767945295 3283080010949761151917943)
        ·
          refine ⟨4924620016424641727876915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283080010949761151917943 4924620016424641727876915)
          ·
            refine ⟨7386930024636962591815373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924620016424641727876915 7386930024636962591815373)
            ·
              refine ⟨2770098759238860971930765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7386930024636962591815373 2770098759238860971930765)
              ·
                refine ⟨1038787034714572864474037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2770098759238860971930765 1038787034714572864474037)
                ·
                  refine ⟨97386284504491206044441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1038787034714572864474037 97386284504491206044441)
                  ·
                    rfl

theorem cell23_1706932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1706932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1706932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1706932 prefixEnd_1706932 := by exact prefixLift 1706932
  have htrace : WordTrace (prefixWord ++ tailWord_1706932) baseStart_1706932 baseEnd_1706932 := by
    simpa [prefixWord, tailWord_1706932, baseEnd_1706932] using wordTrace_append hprefix tailTrace_1706932
  have hstable : (prefixWord ++ tailWord_1706932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1706932).length < 2 ^ (prefixWord ++ tailWord_1706932).sum := by decide
  have hdescent : baseEnd_1706932 < baseStart_1706932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1706932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707009 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 1, 4]
def baseStart_1707009 : Nat := 118140960795 + 1707009 * 2 ^ 59
def prefixEnd_1707009 : Nat := 4983230072969 + 3 ^ 40 * 1707009 * 2
def baseEnd_1707009 : Nat := 292172032850272351045705

theorem tailTrace_1707009 : CollatzResearch.WordTrace tailWord_1707009 prefixEnd_1707009 292172032850272351045705 := by
  unfold tailWord_1707009
  simp only [CollatzResearch.WordTrace]
  refine ⟨62259733072805401772108081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41506488715203601181405387 62259733072805401772108081)
  ·
    refine ⟨46694799804604051329081061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62259733072805401772108081 46694799804604051329081061)
    ·
      refine ⟨8755274963363259624202699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46694799804604051329081061 8755274963363259624202699)
      ·
        refine ⟨13132912445044889436304049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8755274963363259624202699 13132912445044889436304049)
        ·
          refine ⟨9849684333783667077228037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13132912445044889436304049 9849684333783667077228037)
          ·
            refine ⟨1846815812584437576980257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9849684333783667077228037 1846815812584437576980257)
            ·
              refine ⟨1385111859438328182735193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846815812584437576980257 1385111859438328182735193)
              ·
                refine ⟨1038833894578746137051395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385111859438328182735193 1038833894578746137051395)
                ·
                  refine ⟨1558250841868119205577093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1038833894578746137051395 1558250841868119205577093)
                  ·
                    refine ⟨292172032850272351045705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558250841868119205577093 292172032850272351045705)
                    ·
                      rfl

theorem cell23_1707009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_1707009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707009 prefixEnd_1707009 := by exact prefixLift 1707009
  have htrace : WordTrace (prefixWord ++ tailWord_1707009) baseStart_1707009 baseEnd_1707009 := by
    simpa [prefixWord, tailWord_1707009, baseEnd_1707009] using wordTrace_append hprefix tailTrace_1707009
  have hstable : (prefixWord ++ tailWord_1707009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707009).length < 2 ^ (prefixWord ++ tailWord_1707009).sum := by decide
  have hdescent : baseEnd_1707009 < baseStart_1707009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707015 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1707015 : Nat := 118140960795 + 1707015 * 2 ^ 59
def prefixEnd_1707015 : Nat := 4983230072969 + 3 ^ 40 * 1707015 * 2
def baseEnd_1707015 : Nat := 876519179434744029662087

theorem tailTrace_1707015 : CollatzResearch.WordTrace tailWord_1707015 prefixEnd_1707015 876519179434744029662087 := by
  unfold tailWord_1707015
  simp only [CollatzResearch.WordTrace]
  refine ⟨62259951910783664796826499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41506634607189109864550999 62259951910783664796826499)
  ·
    refine ⟨93389927866175497195239749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62259951910783664796826499 93389927866175497195239749)
    ·
      refine ⟨17510611474907905724107453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93389927866175497195239749 17510611474907905724107453)
      ·
        refine ⟨6566479303090464646540295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17510611474907905724107453 6566479303090464646540295)
        ·
          refine ⟨9849718954635696969810443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566479303090464646540295 9849718954635696969810443)
          ·
            refine ⟨14774578431953545454715665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9849718954635696969810443 14774578431953545454715665)
            ·
              refine ⟨11080933823965159091036749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14774578431953545454715665 11080933823965159091036749)
              ·
                refine ⟨4155350183986934659138781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11080933823965159091036749 4155350183986934659138781)
                ·
                  refine ⟨1558256318995100497177043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4155350183986934659138781 1558256318995100497177043)
                  ·
                    refine ⟨2337384478492650745765565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1558256318995100497177043 2337384478492650745765565)
                    ·
                      refine ⟨876519179434744029662087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337384478492650745765565 876519179434744029662087)
                      ·
                        rfl

theorem cell23_1707015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1707015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707015 prefixEnd_1707015 := by exact prefixLift 1707015
  have htrace : WordTrace (prefixWord ++ tailWord_1707015) baseStart_1707015 baseEnd_1707015 := by
    simpa [prefixWord, tailWord_1707015, baseEnd_1707015] using wordTrace_append hprefix tailTrace_1707015
  have hstable : (prefixWord ++ tailWord_1707015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707015).length < 2 ^ (prefixWord ++ tailWord_1707015).sum := by decide
  have hdescent : baseEnd_1707015 < baseStart_1707015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707018 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1707018 : Nat := 118140960795 + 1707018 * 2 ^ 59
def prefixEnd_1707018 : Nat := 4983230072969 + 3 ^ 40 * 1707018 * 2
def baseEnd_1707018 : Nat := 292173573292235839308191

theorem tailTrace_1707018 : CollatzResearch.WordTrace tailWord_1707018 prefixEnd_1707018 292173573292235839308191 := by
  unfold tailWord_1707018
  simp only [CollatzResearch.WordTrace]
  refine ⟨15565015332443199077296427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41506707553181864206123805 15565015332443199077296427)
  ·
    refine ⟨23347522998664798615944641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15565015332443199077296427 23347522998664798615944641)
    ·
      refine ⟨17510642248998598961958481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23347522998664798615944641 17510642248998598961958481)
      ·
        refine ⟨13132981686748949221468861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17510642248998598961958481 13132981686748949221468861)
        ·
          refine ⟨4924868132530855958050823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13132981686748949221468861 4924868132530855958050823)
          ·
            refine ⟨7387302198796283937076235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924868132530855958050823 7387302198796283937076235)
            ·
              refine ⟨11080953298194425905614353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387302198796283937076235 11080953298194425905614353)
              ·
                refine ⟨8310714973645819429210765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11080953298194425905614353 8310714973645819429210765)
                ·
                  refine ⟨3116518115117182285954037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8310714973645819429210765 3116518115117182285954037)
                  ·
                    refine ⟨292173573292235839308191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3116518115117182285954037 292173573292235839308191)
                    ·
                      rfl

theorem cell23_1707018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1707018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707018 prefixEnd_1707018 := by exact prefixLift 1707018
  have htrace : WordTrace (prefixWord ++ tailWord_1707018) baseStart_1707018 baseEnd_1707018 := by
    simpa [prefixWord, tailWord_1707018, baseEnd_1707018] using wordTrace_append hprefix tailTrace_1707018
  have hstable : (prefixWord ++ tailWord_1707018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707018).length < 2 ^ (prefixWord ++ tailWord_1707018).sum := by decide
  have hdescent : baseEnd_1707018 < baseStart_1707018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707042 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 2, 3, 2]
def baseStart_1707042 : Nat := 118140960795 + 1707042 * 2 ^ 59
def prefixEnd_1707042 : Nat := 4983230072969 + 3 ^ 40 * 1707042 * 2
def baseEnd_1707042 : Nat := 876533043412415424024463

theorem tailTrace_1707042 : CollatzResearch.WordTrace tailWord_1707042 prefixEnd_1707042 876533043412415424024463 := by
  unfold tailWord_1707042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15565234170421462102014845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41507291121123898938706253 15565234170421462102014845)
  ·
    refine ⟨5836962813908048288255567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15565234170421462102014845 5836962813908048288255567)
    ·
      refine ⟨8755444220862072432383351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836962813908048288255567 8755444220862072432383351)
      ·
        refine ⟨13133166331293108648575027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8755444220862072432383351 13133166331293108648575027)
        ·
          refine ⟨19699749496939662972862541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13133166331293108648575027 19699749496939662972862541)
          ·
            refine ⟨7387406061352373614823453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19699749496939662972862541 7387406061352373614823453)
            ·
              refine ⟨2770277273007140105558795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7387406061352373614823453 2770277273007140105558795)
              ·
                refine ⟨4155415909510710158338193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770277273007140105558795 4155415909510710158338193)
                ·
                  refine ⟨3116561932133032618753645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4155415909510710158338193 3116561932133032618753645)
                  ·
                    refine ⟨1168710724549887232032617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116561932133032618753645 1168710724549887232032617)
                    ·
                      refine ⟨876533043412415424024463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168710724549887232032617 876533043412415424024463)
                      ·
                        rfl

theorem cell23_1707042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 2, 3, 2].length) (baseStart_1707042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707042 prefixEnd_1707042 := by exact prefixLift 1707042
  have htrace : WordTrace (prefixWord ++ tailWord_1707042) baseStart_1707042 baseEnd_1707042 := by
    simpa [prefixWord, tailWord_1707042, baseEnd_1707042] using wordTrace_append hprefix tailTrace_1707042
  have hstable : (prefixWord ++ tailWord_1707042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707042).length < 2 ^ (prefixWord ++ tailWord_1707042).sum := by decide
  have hdescent : baseEnd_1707042 < baseStart_1707042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707058 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1707058 : Nat := 118140960795 + 1707058 * 2 ^ 59
def prefixEnd_1707058 : Nat := 4983230072969 + 3 ^ 40 * 1707058 * 2
def baseEnd_1707058 : Nat := 876541259102887361424389

theorem tailTrace_1707058 : CollatzResearch.WordTrace tailWord_1707058 prefixEnd_1707058 876541259102887361424389 := by
  unfold tailWord_1707058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15565380062406970785160457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41507680166418588760427885 15565380062406970785160457)
  ·
    refine ⟨11674035046805228088870343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15565380062406970785160457 11674035046805228088870343)
    ·
      refine ⟨17511052570207842133305515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11674035046805228088870343 17511052570207842133305515)
      ·
        refine ⟨26266578855311763199958273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17511052570207842133305515 26266578855311763199958273)
        ·
          refine ⟨19699934141483822399968705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26266578855311763199958273 19699934141483822399968705)
          ·
            refine ⟨14774950606112866799976529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19699934141483822399968705 14774950606112866799976529)
            ·
              refine ⟨11081212954584650099982397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14774950606112866799976529 11081212954584650099982397)
              ·
                refine ⟨4155454857969243787493399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11081212954584650099982397 4155454857969243787493399)
                ·
                  refine ⟨6233182286953865681240099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155454857969243787493399 6233182286953865681240099)
                  ·
                    refine ⟨9349773430430798521860149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6233182286953865681240099 9349773430430798521860149)
                    ·
                      refine ⟨876541259102887361424389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9349773430430798521860149 876541259102887361424389)
                      ·
                        rfl

theorem cell23_1707058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1707058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707058 prefixEnd_1707058 := by exact prefixLift 1707058
  have htrace : WordTrace (prefixWord ++ tailWord_1707058) baseStart_1707058 baseEnd_1707058 := by
    simpa [prefixWord, tailWord_1707058, baseEnd_1707058] using wordTrace_append hprefix tailTrace_1707058
  have hstable : (prefixWord ++ tailWord_1707058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707058).length < 2 ^ (prefixWord ++ tailWord_1707058).sum := by decide
  have hdescent : baseEnd_1707058 < baseStart_1707058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707065 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 4, 4]
def baseStart_1707065 : Nat := 118140960795 + 1707065 * 2 ^ 59
def prefixEnd_1707065 : Nat := 4983230072969 + 3 ^ 40 * 1707065 * 2
def baseEnd_1707065 : Nat := 292181617822489611345619

theorem tailTrace_1707065 : CollatzResearch.WordTrace tailWord_1707065 prefixEnd_1707065 292181617822489611345619 := by
  unfold tailWord_1707065
  simp only [CollatzResearch.WordTrace]
  refine ⟨62261775560602523336146649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41507850373735015557431099 62261775560602523336146649)
  ·
    refine ⟨46696331670451892502109987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62261775560602523336146649 46696331670451892502109987)
    ·
      refine ⟨70044497505677838753164981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46696331670451892502109987 70044497505677838753164981)
      ·
        refine ⟨6566671641157297383109217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70044497505677838753164981 6566671641157297383109217)
        ·
          refine ⟨4925003730867973037331913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6566671641157297383109217 4925003730867973037331913)
          ·
            refine ⟨3693752798150979777998935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4925003730867973037331913 3693752798150979777998935)
            ·
              refine ⟨5540629197226469666998403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693752798150979777998935 5540629197226469666998403)
              ·
                refine ⟨8310943795839704500497605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5540629197226469666998403 8310943795839704500497605)
                ·
                  refine ⟨1558301961719944593843301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8310943795839704500497605 1558301961719944593843301)
                  ·
                    refine ⟨292181617822489611345619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558301961719944593843301 292181617822489611345619)
                    ·
                      rfl

theorem cell23_1707065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 4].length) (baseStart_1707065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707065 prefixEnd_1707065 := by exact prefixLift 1707065
  have htrace : WordTrace (prefixWord ++ tailWord_1707065) baseStart_1707065 baseEnd_1707065 := by
    simpa [prefixWord, tailWord_1707065, baseEnd_1707065] using wordTrace_append hprefix tailTrace_1707065
  have hstable : (prefixWord ++ tailWord_1707065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707065).length < 2 ^ (prefixWord ++ tailWord_1707065).sum := by decide
  have hdescent : baseEnd_1707065 < baseStart_1707065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707071 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1707071 : Nat := 118140960795 + 1707071 * 2 ^ 59
def prefixEnd_1707071 : Nat := 4983230072969 + 3 ^ 40 * 1707071 * 2
def baseEnd_1707071 : Nat := 876547934351395810561829

theorem tailTrace_1707071 : CollatzResearch.WordTrace tailWord_1707071 prefixEnd_1707071 876547934351395810561829 := by
  unfold tailWord_1707071
  simp only [CollatzResearch.WordTrace]
  refine ⟨62261994398580786360865067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41507996265720524240576711 62261994398580786360865067)
  ·
    refine ⟨93392991597871179541297601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62261994398580786360865067 93392991597871179541297601)
    ·
      refine ⟨70044743698403384655973201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93392991597871179541297601 70044743698403384655973201)
      ·
        refine ⟨52533557773802538491979901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70044743698403384655973201 52533557773802538491979901)
        ·
          refine ⟨19700084165175951934492463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52533557773802538491979901 19700084165175951934492463)
          ·
            refine ⟨29550126247763927901738695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19700084165175951934492463 29550126247763927901738695)
            ·
              refine ⟨44325189371645891852608043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29550126247763927901738695 44325189371645891852608043)
              ·
                refine ⟨66487784057468837778912065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44325189371645891852608043 66487784057468837778912065)
                ·
                  refine ⟨49865838043101628334184049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66487784057468837778912065 49865838043101628334184049)
                  ·
                    refine ⟨37399378532326221250638037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49865838043101628334184049 37399378532326221250638037)
                    ·
                      refine ⟨876547934351395810561829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37399378532326221250638037 876547934351395810561829)
                      ·
                        rfl

theorem cell23_1707071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1707071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707071 prefixEnd_1707071 := by exact prefixLift 1707071
  have htrace : WordTrace (prefixWord ++ tailWord_1707071) baseStart_1707071 baseEnd_1707071 := by
    simpa [prefixWord, tailWord_1707071, baseEnd_1707071] using wordTrace_append hprefix tailTrace_1707071
  have hstable : (prefixWord ++ tailWord_1707071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707071).length < 2 ^ (prefixWord ++ tailWord_1707071).sum := by decide
  have hdescent : baseEnd_1707071 < baseStart_1707071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707072 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 3, 2, 2]
def baseStart_1707072 : Nat := 118140960795 + 1707072 * 2 ^ 59
def prefixEnd_1707072 : Nat := 4983230072969 + 3 ^ 40 * 1707072 * 2
def baseEnd_1707072 : Nat := 876548447832050306649325

theorem tailTrace_1707072 : CollatzResearch.WordTrace tailWord_1707072 prefixEnd_1707072 876548447832050306649325 := by
  unfold tailWord_1707072
  simp only [CollatzResearch.WordTrace]
  refine ⟨31131015435788581765825735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41508020581051442354434313 31131015435788581765825735)
  ·
    refine ⟨46696523153682872648738603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31131015435788581765825735 46696523153682872648738603)
    ·
      refine ⟨70044784730524308973107905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46696523153682872648738603 70044784730524308973107905)
      ·
        refine ⟨52533588547893231729830929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70044784730524308973107905 52533588547893231729830929)
        ·
          refine ⟨39400191410919923797373197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52533588547893231729830929 39400191410919923797373197)
          ·
            refine ⟨14775071779094971424014949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39400191410919923797373197 14775071779094971424014949)
            ·
              refine ⟨2770325958580307142002803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14775071779094971424014949 2770325958580307142002803)
              ·
                refine ⟨4155488937870460713004205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770325958580307142002803 4155488937870460713004205)
                ·
                  refine ⟨1558308351701422767376577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4155488937870460713004205 1558308351701422767376577)
                  ·
                    refine ⟨1168731263776067075532433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558308351701422767376577 1168731263776067075532433)
                    ·
                      refine ⟨876548447832050306649325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168731263776067075532433 876548447832050306649325)
                      ·
                        rfl

theorem cell23_1707072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_1707072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707072 prefixEnd_1707072 := by exact prefixLift 1707072
  have htrace : WordTrace (prefixWord ++ tailWord_1707072) baseStart_1707072 baseEnd_1707072 := by
    simpa [prefixWord, tailWord_1707072, baseEnd_1707072] using wordTrace_append hprefix tailTrace_1707072
  have hstable : (prefixWord ++ tailWord_1707072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707072).length < 2 ^ (prefixWord ++ tailWord_1707072).sum := by decide
  have hdescent : baseEnd_1707072 < baseStart_1707072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707081 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 6]
def baseStart_1707081 : Nat := 118140960795 + 1707081 * 2 ^ 59
def prefixEnd_1707081 : Nat := 4983230072969 + 3 ^ 40 * 1707081 * 2
def baseEnd_1707081 : Nat := 876553069157940771436783

theorem tailTrace_1707081 : CollatzResearch.WordTrace tailWord_1707081 prefixEnd_1707081 876553069157940771436783 := by
  unfold tailWord_1707081
  simp only [CollatzResearch.WordTrace]
  refine ⟨62262359128544558068729097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41508239419029705379152731 62262359128544558068729097)
  ·
    refine ⟨46696769346408418551546823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62262359128544558068729097 46696769346408418551546823)
    ·
      refine ⟨70045154019612627827320235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46696769346408418551546823 70045154019612627827320235)
      ·
        refine ⟨105067731029418941740980353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70045154019612627827320235 105067731029418941740980353)
        ·
          refine ⟨78800798272064206305735265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105067731029418941740980353 78800798272064206305735265)
          ·
            refine ⟨59100598704048154729301449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78800798272064206305735265 59100598704048154729301449)
            ·
              refine ⟨44325449028036116046976087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59100598704048154729301449 44325449028036116046976087)
              ·
                refine ⟨66488173542054174070464131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44325449028036116046976087 66488173542054174070464131)
                ·
                  refine ⟨99732260313081261105696197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66488173542054174070464131 99732260313081261105696197)
                  ·
                    refine ⟨18699798808702736457318037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99732260313081261105696197 18699798808702736457318037)
                    ·
                      refine ⟨876553069157940771436783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18699798808702736457318037 876553069157940771436783)
                      ·
                        rfl

theorem cell23_1707081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_1707081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707081 prefixEnd_1707081 := by exact prefixLift 1707081
  have htrace : WordTrace (prefixWord ++ tailWord_1707081) baseStart_1707081 baseEnd_1707081 := by
    simpa [prefixWord, tailWord_1707081, baseEnd_1707081] using wordTrace_append hprefix tailTrace_1707081
  have hstable : (prefixWord ++ tailWord_1707081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707081).length < 2 ^ (prefixWord ++ tailWord_1707081).sum := by decide
  have hdescent : baseEnd_1707081 < baseStart_1707081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707085 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1707085 : Nat := 118140960795 + 1707085 * 2 ^ 59
def prefixEnd_1707085 : Nat := 4983230072969 + 3 ^ 40 * 1707085 * 2
def baseEnd_1707085 : Nat := 876555123080558755786765

theorem tailTrace_1707085 : CollatzResearch.WordTrace tailWord_1707085 prefixEnd_1707085 876555123080558755786765 := by
  unfold tailWord_1707085
  simp only [CollatzResearch.WordTrace]
  refine ⟨62262505020530066751874709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41508336680353377834583139 62262505020530066751874709)
  ·
    refine ⟨2918554922837346878994127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62262505020530066751874709 2918554922837346878994127)
    ·
      refine ⟨4377832384256020318491191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918554922837346878994127 4377832384256020318491191)
      ·
        refine ⟨6566748576384030477736787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377832384256020318491191 6566748576384030477736787)
        ·
          refine ⟨9850122864576045716605181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566748576384030477736787 9850122864576045716605181)
          ·
            refine ⟨3693796074216017143726943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9850122864576045716605181 3693796074216017143726943)
            ·
              refine ⟨5540694111324025715590415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693796074216017143726943 5540694111324025715590415)
              ·
                refine ⟨8311041166986038573385623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5540694111324025715590415 8311041166986038573385623)
                ·
                  refine ⟨12466561750479057860078435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8311041166986038573385623 12466561750479057860078435)
                  ·
                    refine ⟨18699842625718586790117653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12466561750479057860078435 18699842625718586790117653)
                    ·
                      refine ⟨876555123080558755786765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18699842625718586790117653 876555123080558755786765)
                      ·
                        rfl

theorem cell23_1707085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1707085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707085 prefixEnd_1707085 := by exact prefixLift 1707085
  have htrace : WordTrace (prefixWord ++ tailWord_1707085) baseStart_1707085 baseEnd_1707085 := by
    simpa [prefixWord, tailWord_1707085, baseEnd_1707085] using wordTrace_append hprefix tailTrace_1707085
  have hstable : (prefixWord ++ tailWord_1707085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707085).length < 2 ^ (prefixWord ++ tailWord_1707085).sum := by decide
  have hdescent : baseEnd_1707085 < baseStart_1707085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707091 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 4, 7]
def baseStart_1707091 : Nat := 118140960795 + 1707091 * 2 ^ 59
def prefixEnd_1707091 : Nat := 4983230072969 + 3 ^ 40 * 1707091 * 2
def baseEnd_1707091 : Nat := 292186067988161910770579

theorem tailTrace_1707091 : CollatzResearch.WordTrace tailWord_1707091 prefixEnd_1707091 292186067988161910770579 := by
  unfold tailWord_1707091
  simp only [CollatzResearch.WordTrace]
  refine ⟨62262723858508329776593127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41508482572338886517728751 62262723858508329776593127)
  ·
    refine ⟨93394085787762494664889691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62262723858508329776593127 93394085787762494664889691)
    ·
      refine ⟨140091128681643741997334537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93394085787762494664889691 140091128681643741997334537)
      ·
        refine ⟨105068346511232806498000903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140091128681643741997334537 105068346511232806498000903)
        ·
          refine ⟨157602519766849209747001355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105068346511232806498000903 157602519766849209747001355)
          ·
            refine ⟨236403779650273814620502033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157602519766849209747001355 236403779650273814620502033)
            ·
              refine ⟨177302834737705360965376525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236403779650273814620502033 177302834737705360965376525)
              ·
                refine ⟨66488563026639510362016197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177302834737705360965376525 66488563026639510362016197)
                ·
                  refine ⟨12466605567494908192878037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66488563026639510362016197 12466605567494908192878037)
                  ·
                    refine ⟨292186067988161910770579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12466605567494908192878037 292186067988161910770579)
                    ·
                      rfl

theorem cell23_1707091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_1707091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707091 prefixEnd_1707091 := by exact prefixLift 1707091
  have htrace : WordTrace (prefixWord ++ tailWord_1707091) baseStart_1707091 baseEnd_1707091 := by
    simpa [prefixWord, tailWord_1707091, baseEnd_1707091] using wordTrace_append hprefix tailTrace_1707091
  have hstable : (prefixWord ++ tailWord_1707091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707091).length < 2 ^ (prefixWord ++ tailWord_1707091).sum := by decide
  have hdescent : baseEnd_1707091 < baseStart_1707091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707105 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 3]
def baseStart_1707105 : Nat := 118140960795 + 1707105 * 2 ^ 59
def prefixEnd_1707105 : Nat := 4983230072969 + 3 ^ 40 * 1707105 * 2
def baseEnd_1707105 : Nat := 876565392693648677536673

theorem tailTrace_1707105 : CollatzResearch.WordTrace tailWord_1707105 prefixEnd_1707105 876565392693648677536673 := by
  unfold tailWord_1707105
  simp only [CollatzResearch.WordTrace]
  refine ⟨62263234480457610167602769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41508822986971740111735179 62263234480457610167602769)
  ·
    refine ⟨46697425860343207625702077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62263234480457610167602769 46697425860343207625702077)
    ·
      refine ⟨17511534697628702859638279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46697425860343207625702077 17511534697628702859638279)
      ·
        refine ⟨26267302046443054289457419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17511534697628702859638279 26267302046443054289457419)
        ·
          refine ⟨39400953069664581434186129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26267302046443054289457419 39400953069664581434186129)
          ·
            refine ⟨29550714802248436075639597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39400953069664581434186129 29550714802248436075639597)
            ·
              refine ⟨11081518050843163528364849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29550714802248436075639597 11081518050843163528364849)
              ·
                refine ⟨8311138538132372646273637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11081518050843163528364849 8311138538132372646273637)
                ·
                  refine ⟨1558338475899819871176307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8311138538132372646273637 1558338475899819871176307)
                  ·
                    refine ⟨2337507713849729806764461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1558338475899819871176307 2337507713849729806764461)
                    ·
                      refine ⟨876565392693648677536673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337507713849729806764461 876565392693648677536673)
                      ·
                        rfl

theorem cell23_1707105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_1707105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707105 prefixEnd_1707105 := by exact prefixLift 1707105
  have htrace : WordTrace (prefixWord ++ tailWord_1707105) baseStart_1707105 baseEnd_1707105 := by
    simpa [prefixWord, tailWord_1707105, baseEnd_1707105] using wordTrace_append hprefix tailTrace_1707105
  have hstable : (prefixWord ++ tailWord_1707105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707105).length < 2 ^ (prefixWord ++ tailWord_1707105).sum := by decide
  have hdescent : baseEnd_1707105 < baseStart_1707105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707112 : List Nat := [2, 1, 4, 4, 2, 1, 9]
def baseStart_1707112 : Nat := 118140960795 + 1707112 * 2 ^ 59
def prefixEnd_1707112 : Nat := 4983230072969 + 3 ^ 40 * 1707112 * 2
def baseEnd_1707112 : Nat := 10821839346397903088261

theorem tailTrace_1707112 : CollatzResearch.WordTrace tailWord_1707112 prefixEnd_1707112 10821839346397903088261 := by
  unfold tailWord_1707112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31131744895716125181553795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41508993194288166908738393 31131744895716125181553795)
  ·
    refine ⟨46697617343574187772330693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31131744895716125181553795 46697617343574187772330693)
    ·
      refine ⟨8755803251920160207312005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46697617343574187772330693 8755803251920160207312005)
      ·
        refine ⟨1641713109735030038871001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8755803251920160207312005 1641713109735030038871001)
        ·
          refine ⟨1231284832301272529153251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641713109735030038871001 1231284832301272529153251)
          ·
            refine ⟨1846927248451908793729877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231284832301272529153251 1846927248451908793729877)
            ·
              refine ⟨10821839346397903088261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1846927248451908793729877 10821839346397903088261)
              ·
                rfl

theorem cell23_1707112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 9].length) (baseStart_1707112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707112 prefixEnd_1707112 := by exact prefixLift 1707112
  have htrace : WordTrace (prefixWord ++ tailWord_1707112) baseStart_1707112 baseEnd_1707112 := by
    simpa [prefixWord, tailWord_1707112, baseEnd_1707112] using wordTrace_append hprefix tailTrace_1707112
  have hstable : (prefixWord ++ tailWord_1707112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707112).length < 2 ^ (prefixWord ++ tailWord_1707112).sum := by decide
  have hdescent : baseEnd_1707112 < baseStart_1707112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707122 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1707122 : Nat := 118140960795 + 1707122 * 2 ^ 59
def prefixEnd_1707122 : Nat := 4983230072969 + 3 ^ 40 * 1707122 * 2
def baseEnd_1707122 : Nat := 876574121864775111024095

theorem tailTrace_1707122 : CollatzResearch.WordTrace tailWord_1707122 prefixEnd_1707122 876574121864775111024095 := by
  unfold tailWord_1707122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15565963630349005517742905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41509236347597348047314413 15565963630349005517742905)
  ·
    refine ⟨11674472722761754138307179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15565963630349005517742905 11674472722761754138307179)
    ·
      refine ⟨17511709084142631207460769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11674472722761754138307179 17511709084142631207460769)
      ·
        refine ⟨13133781813106973405595577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17511709084142631207460769 13133781813106973405595577)
        ·
          refine ⟨9850336359830230054196683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13133781813106973405595577 9850336359830230054196683)
          ·
            refine ⟨14775504539745345081295025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850336359830230054196683 14775504539745345081295025)
            ·
              refine ⟨11081628404809008810971269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14775504539745345081295025 11081628404809008810971269)
              ·
                refine ⟨2077805325901689152057113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11081628404809008810971269 2077805325901689152057113)
                ·
                  refine ⟨1558353994426266864042835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2077805325901689152057113 1558353994426266864042835)
                  ·
                    refine ⟨2337530991639400296064253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1558353994426266864042835 2337530991639400296064253)
                    ·
                      refine ⟨876574121864775111024095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337530991639400296064253 876574121864775111024095)
                      ·
                        rfl

theorem cell23_1707122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1707122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707122 prefixEnd_1707122 := by exact prefixLift 1707122
  have htrace : WordTrace (prefixWord ++ tailWord_1707122) baseStart_1707122 baseEnd_1707122 := by
    simpa [prefixWord, tailWord_1707122, baseEnd_1707122] using wordTrace_append hprefix tailTrace_1707122
  have hstable : (prefixWord ++ tailWord_1707122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707122).length < 2 ^ (prefixWord ++ tailWord_1707122).sum := by decide
  have hdescent : baseEnd_1707122 < baseStart_1707122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707162 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1707162 : Nat := 118140960795 + 1707162 * 2 ^ 59
def prefixEnd_1707162 : Nat := 4983230072969 + 3 ^ 40 * 1707162 * 2
def baseEnd_1707162 : Nat := 876594661090954954523911

theorem tailTrace_1707162 : CollatzResearch.WordTrace tailWord_1707162 prefixEnd_1707162 876594661090954954523911 := by
  unfold tailWord_1707162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566328360312777225606935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41510208960834072601618493 15566328360312777225606935)
  ·
    refine ⟨23349492540469165838410403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15566328360312777225606935 23349492540469165838410403)
    ·
      refine ⟨35024238810703748757615605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23349492540469165838410403 35024238810703748757615605)
      ·
        refine ⟨3283522388503476446026463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35024238810703748757615605 3283522388503476446026463)
        ·
          refine ⟨4925283582755214669039695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283522388503476446026463 4925283582755214669039695)
          ·
            refine ⟨7387925374132822003559543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925283582755214669039695 7387925374132822003559543)
            ·
              refine ⟨11081888061199233005339315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387925374132822003559543 11081888061199233005339315)
              ·
                refine ⟨16622832091798849508008973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11081888061199233005339315 16622832091798849508008973)
                ·
                  refine ⟨6233562034424568565503365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16622832091798849508008973 6233562034424568565503365)
                  ·
                    refine ⟨1168792881454606606031881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6233562034424568565503365 1168792881454606606031881)
                    ·
                      refine ⟨876594661090954954523911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168792881454606606031881 876594661090954954523911)
                      ·
                        rfl

theorem cell23_1707162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1707162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707162 prefixEnd_1707162 := by exact prefixLift 1707162
  have htrace : WordTrace (prefixWord ++ tailWord_1707162) baseStart_1707162 baseEnd_1707162 := by
    simpa [prefixWord, tailWord_1707162, baseEnd_1707162] using wordTrace_append hprefix tailTrace_1707162
  have hstable : (prefixWord ++ tailWord_1707162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707162).length < 2 ^ (prefixWord ++ tailWord_1707162).sum := by decide
  have hdescent : baseEnd_1707162 < baseStart_1707162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707205 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 4, 5, 2]
def baseStart_1707205 : Nat := 118140960795 + 1707205 * 2 ^ 59
def prefixEnd_1707205 : Nat := 4983230072969 + 3 ^ 40 * 1707205 * 2
def baseEnd_1707205 : Nat := 876616740759098286286213

theorem tailTrace_1707205 : CollatzResearch.WordTrace tailWord_1707205 prefixEnd_1707205 876616740759098286286213 := by
  unfold tailWord_1707205
  simp only [CollatzResearch.WordTrace]
  refine ⟨62266881780095327246243069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41511254520063551497495379 62266881780095327246243069)
  ·
    refine ⟨23350080667535747717341151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62266881780095327246243069 23350080667535747717341151)
    ·
      refine ⟨35025121001303621576011727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23350080667535747717341151 35025121001303621576011727)
      ·
        refine ⟨52537681501955432364017591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35025121001303621576011727 52537681501955432364017591)
        ·
          refine ⟨78806522252933148546026387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52537681501955432364017591 78806522252933148546026387)
          ·
            refine ⟨118209783379399722819039581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78806522252933148546026387 118209783379399722819039581)
            ·
              refine ⟨44328668767274896057139843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118209783379399722819039581 44328668767274896057139843)
              ·
                refine ⟨66493003150912344085709765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44328668767274896057139843 66493003150912344085709765)
                ·
                  refine ⟨12467438090796064516070581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66493003150912344085709765 12467438090796064516070581)
                  ·
                    refine ⟨1168822321012131048381617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12467438090796064516070581 1168822321012131048381617)
                    ·
                      refine ⟨876616740759098286286213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168822321012131048381617 876616740759098286286213)
                      ·
                        rfl

theorem cell23_1707205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_1707205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707205 prefixEnd_1707205 := by exact prefixLift 1707205
  have htrace : WordTrace (prefixWord ++ tailWord_1707205) baseStart_1707205 baseEnd_1707205 := by
    simpa [prefixWord, tailWord_1707205, baseEnd_1707205] using wordTrace_append hprefix tailTrace_1707205
  have hstable : (prefixWord ++ tailWord_1707205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707205).length < 2 ^ (prefixWord ++ tailWord_1707205).sum := by decide
  have hdescent : baseEnd_1707205 < baseStart_1707205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707208 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_1707208 : Nat := 118140960795 + 1707208 * 2 ^ 59
def prefixEnd_1707208 : Nat := 4983230072969 + 3 ^ 40 * 1707208 * 2
def baseEnd_1707208 : Nat := 876618281201061774548699

theorem tailTrace_1707208 : CollatzResearch.WordTrace tailWord_1707208 prefixEnd_1707208 876618281201061774548699 := by
  unfold tailWord_1707208
  simp only [CollatzResearch.WordTrace]
  refine ⟨31133495599542229379301139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41511327466056305839068185 31133495599542229379301139)
  ·
    refine ⟨46700243399313344068951709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31133495599542229379301139 46700243399313344068951709)
    ·
      refine ⟨17512591274742504025856891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46700243399313344068951709 17512591274742504025856891)
      ·
        refine ⟨26268886912113756038785337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17512591274742504025856891 26268886912113756038785337)
        ·
          refine ⟨19701665184085317029089003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26268886912113756038785337 19701665184085317029089003)
          ·
            refine ⟨29552497776127975543633505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19701665184085317029089003 29552497776127975543633505)
            ·
              refine ⟨22164373332095981657725129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29552497776127975543633505 22164373332095981657725129)
              ·
                refine ⟨16623279999071986243293847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22164373332095981657725129 16623279999071986243293847)
                ·
                  refine ⟨24934919998607979364940771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16623279999071986243293847 24934919998607979364940771)
                  ·
                    refine ⟨37402379997911969047411157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24934919998607979364940771 37402379997911969047411157)
                    ·
                      refine ⟨876618281201061774548699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37402379997911969047411157 876618281201061774548699)
                      ·
                        rfl

theorem cell23_1707208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_1707208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707208 prefixEnd_1707208 := by exact prefixLift 1707208
  have htrace : WordTrace (prefixWord ++ tailWord_1707208) baseStart_1707208 baseEnd_1707208 := by
    simpa [prefixWord, tailWord_1707208, baseEnd_1707208] using wordTrace_append hprefix tailTrace_1707208
  have hstable : (prefixWord ++ tailWord_1707208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707208).length < 2 ^ (prefixWord ++ tailWord_1707208).sum := by decide
  have hdescent : baseEnd_1707208 < baseStart_1707208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707255 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_1707255 : Nat := 118140960795 + 1707255 * 2 ^ 59
def prefixEnd_1707255 : Nat := 4983230072969 + 3 ^ 40 * 1707255 * 2
def baseEnd_1707255 : Nat := 876642414791823090660983

theorem tailTrace_1707255 : CollatzResearch.WordTrace tailWord_1707255 prefixEnd_1707255 876642414791823090660983 := by
  unfold tailWord_1707255
  simp only [CollatzResearch.WordTrace]
  refine ⟨62268705429914185785563219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41512470286609457190375479 62268705429914185785563219)
  ·
    refine ⟨93403058144871278678344829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62268705429914185785563219 93403058144871278678344829)
    ·
      refine ⟨35026146804326729504379311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93403058144871278678344829 35026146804326729504379311)
      ·
        refine ⟨52539220206490094256568967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35026146804326729504379311 52539220206490094256568967)
        ·
          refine ⟨78808830309735141384853451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52539220206490094256568967 78808830309735141384853451)
          ·
            refine ⟨118213245464602712077280177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78808830309735141384853451 118213245464602712077280177)
            ·
              refine ⟨88659934098452034057960133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118213245464602712077280177 88659934098452034057960133)
              ·
                refine ⟨16623737643459756385867525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88659934098452034057960133 16623737643459756385867525)
                ·
                  refine ⟨3116950808148704322350161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16623737643459756385867525 3116950808148704322350161)
                  ·
                    refine ⟨2337713106111528241762621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3116950808148704322350161 2337713106111528241762621)
                    ·
                      refine ⟨876642414791823090660983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337713106111528241762621 876642414791823090660983)
                      ·
                        rfl

theorem cell23_1707255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_1707255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707255 prefixEnd_1707255 := by exact prefixLift 1707255
  have htrace : WordTrace (prefixWord ++ tailWord_1707255) baseStart_1707255 baseEnd_1707255 := by
    simpa [prefixWord, tailWord_1707255, baseEnd_1707255] using wordTrace_append hprefix tailTrace_1707255
  have hstable : (prefixWord ++ tailWord_1707255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707255).length < 2 ^ (prefixWord ++ tailWord_1707255).sum := by decide
  have hdescent : baseEnd_1707255 < baseStart_1707255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707296 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 3, 4]
def baseStart_1707296 : Nat := 118140960795 + 1707296 * 2 ^ 59
def prefixEnd_1707296 : Nat := 4983230072969 + 3 ^ 40 * 1707296 * 2
def baseEnd_1707296 : Nat := 292221155832885810082765

theorem tailTrace_1707296 : CollatzResearch.WordTrace tailWord_1707296 prefixEnd_1707296 292221155832885810082765 := by
  unfold tailWord_1707296
  simp only [CollatzResearch.WordTrace]
  refine ⟨31135100411382824893902871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41513467215177099858537161 31135100411382824893902871)
  ·
    refine ⟨46702650617074237340854307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31135100411382824893902871 46702650617074237340854307)
    ·
      refine ⟨70053975925611356011281461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46702650617074237340854307 70053975925611356011281461)
      ·
        refine ⟨6567560243026064626057637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70053975925611356011281461 6567560243026064626057637)
        ·
          refine ⟨1231417545567387117385807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6567560243026064626057637 1231417545567387117385807)
          ·
            refine ⟨1847126318351080676078711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231417545567387117385807 1847126318351080676078711)
            ·
              refine ⟨2770689477526621014118067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847126318351080676078711 2770689477526621014118067)
              ·
                refine ⟨4156034216289931521177101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770689477526621014118067 4156034216289931521177101)
                ·
                  refine ⟨1558512831108724320441413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4156034216289931521177101 1558512831108724320441413)
                  ·
                    refine ⟨292221155832885810082765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1558512831108724320441413 292221155832885810082765)
                    ·
                      rfl

theorem cell23_1707296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 3, 4].length) (baseStart_1707296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707296 prefixEnd_1707296 := by exact prefixLift 1707296
  have htrace : WordTrace (prefixWord ++ tailWord_1707296) baseStart_1707296 baseEnd_1707296 := by
    simpa [prefixWord, tailWord_1707296, baseEnd_1707296] using wordTrace_append hprefix tailTrace_1707296
  have hstable : (prefixWord ++ tailWord_1707296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707296).length < 2 ^ (prefixWord ++ tailWord_1707296).sum := by decide
  have hdescent : baseEnd_1707296 < baseStart_1707296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707309 : List Nat := [1, 5, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1707309 : Nat := 118140960795 + 1707309 * 2 ^ 59
def prefixEnd_1707309 : Nat := 4983230072969 + 3 ^ 40 * 1707309 * 2
def baseEnd_1707309 : Nat := 97407793638573986598415

theorem tailTrace_1707309 : CollatzResearch.WordTrace tailWord_1707309 prefixEnd_1707309 97407793638573986598415 := by
  unfold tailWord_1707309
  simp only [CollatzResearch.WordTrace]
  refine ⟨62270674971718553008028981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41513783314479035338685987 62270674971718553008028981)
  ·
    refine ⟨5837875778598614344502717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62270674971718553008028981 5837875778598614344502717)
    ·
      refine ⟨2189203416974480379188519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5837875778598614344502717 2189203416974480379188519)
      ·
        refine ⟨3283805125461720568782779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189203416974480379188519 3283805125461720568782779)
        ·
          refine ⟨4925707688192580853174169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283805125461720568782779 4925707688192580853174169)
          ·
            refine ⟨3694280766144435639880627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4925707688192580853174169 3694280766144435639880627)
            ·
              refine ⟨5541421149216653459820941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694280766144435639880627 5541421149216653459820941)
              ·
                refine ⟨2078032930956245047432853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5541421149216653459820941 2078032930956245047432853)
                ·
                  refine ⟨97407793638573986598415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2078032930956245047432853 97407793638573986598415)
                  ·
                    rfl

theorem cell23_1707309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1707309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707309 prefixEnd_1707309 := by exact prefixLift 1707309
  have htrace : WordTrace (prefixWord ++ tailWord_1707309) baseStart_1707309 baseEnd_1707309 := by
    simpa [prefixWord, tailWord_1707309, baseEnd_1707309] using wordTrace_append hprefix tailTrace_1707309
  have hstable : (prefixWord ++ tailWord_1707309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707309).length < 2 ^ (prefixWord ++ tailWord_1707309).sum := by decide
  have hdescent : baseEnd_1707309 < baseStart_1707309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707312 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 4, 3, 2]
def baseStart_1707312 : Nat := 118140960795 + 1707312 * 2 ^ 59
def prefixEnd_1707312 : Nat := 4983230072969 + 3 ^ 40 * 1707312 * 2
def baseEnd_1707312 : Nat := 876671683189129367648221

theorem tailTrace_1707312 : CollatzResearch.WordTrace tailWord_1707312 prefixEnd_1707312 876671683189129367648221 := by
  unfold tailWord_1707312
  simp only [CollatzResearch.WordTrace]
  refine ⟨31135392195353842260194095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41513856260471789680258793 31135392195353842260194095)
  ·
    refine ⟨46703088293030763390291143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31135392195353842260194095 46703088293030763390291143)
    ·
      refine ⟨70054632439546145085436715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46703088293030763390291143 70054632439546145085436715)
      ·
        refine ⟨105081948659319217628155073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70054632439546145085436715 105081948659319217628155073)
        ·
          refine ⟨78811461494489413221116305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105081948659319217628155073 78811461494489413221116305)
          ·
            refine ⟨59108596120867059915837229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78811461494489413221116305 59108596120867059915837229)
            ·
              refine ⟨22165723545325147468438961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59108596120867059915837229 22165723545325147468438961)
              ·
                refine ⟨16624292658993860601329221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22165723545325147468438961 16624292658993860601329221)
                ·
                  refine ⟨3117054873561348862749229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16624292658993860601329221 3117054873561348862749229)
                  ·
                    refine ⟨1168895577585505823530961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117054873561348862749229 1168895577585505823530961)
                    ·
                      refine ⟨876671683189129367648221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168895577585505823530961 876671683189129367648221)
                      ·
                        rfl

theorem cell23_1707312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 4, 3, 2].length) (baseStart_1707312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707312 prefixEnd_1707312 := by exact prefixLift 1707312
  have htrace : WordTrace (prefixWord ++ tailWord_1707312) baseStart_1707312 baseEnd_1707312 := by
    simpa [prefixWord, tailWord_1707312, baseEnd_1707312] using wordTrace_append hprefix tailTrace_1707312
  have hstable : (prefixWord ++ tailWord_1707312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707312).length < 2 ^ (prefixWord ++ tailWord_1707312).sum := by decide
  have hdescent : baseEnd_1707312 < baseStart_1707312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707335 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1707335 : Nat := 118140960795 + 1707335 * 2 ^ 59
def prefixEnd_1707335 : Nat := 4983230072969 + 3 ^ 40 * 1707335 * 2
def baseEnd_1707335 : Nat := 292227831081394259220205

theorem tailTrace_1707335 : CollatzResearch.WordTrace tailWord_1707335 prefixEnd_1707335 292227831081394259220205 := by
  unfold tailWord_1707335
  simp only [CollatzResearch.WordTrace]
  refine ⟨62271623269624359448475459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41514415513082906298983639 62271623269624359448475459)
  ·
    refine ⟨93407434904436539172713189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62271623269624359448475459 93407434904436539172713189)
    ·
      refine ⟨17513894044581851094883723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93407434904436539172713189 17513894044581851094883723)
      ·
        refine ⟨26270841066872776642325585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17513894044581851094883723 26270841066872776642325585)
        ·
          refine ⟨19703130800154582481744189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26270841066872776642325585 19703130800154582481744189)
          ·
            refine ⟨7388674050057968430654071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19703130800154582481744189 7388674050057968430654071)
            ·
              refine ⟨11083011075086952645981107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388674050057968430654071 11083011075086952645981107)
              ·
                refine ⟨16624516612630428968971661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083011075086952645981107 16624516612630428968971661)
                ·
                  refine ⟨6234193729736410863364373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16624516612630428968971661 6234193729736410863364373)
                  ·
                    refine ⟨292227831081394259220205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6234193729736410863364373 292227831081394259220205)
                    ·
                      rfl

theorem cell23_1707335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1707335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707335 prefixEnd_1707335 := by exact prefixLift 1707335
  have htrace : WordTrace (prefixWord ++ tailWord_1707335) baseStart_1707335 baseEnd_1707335 := by
    simpa [prefixWord, tailWord_1707335, baseEnd_1707335] using wordTrace_append hprefix tailTrace_1707335
  have hstable : (prefixWord ++ tailWord_1707335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707335).length < 2 ^ (prefixWord ++ tailWord_1707335).sum := by decide
  have hdescent : baseEnd_1707335 < baseStart_1707335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707359 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 3, 2, 2]
def baseStart_1707359 : Nat := 118140960795 + 1707359 * 2 ^ 59
def prefixEnd_1707359 : Nat := 4983230072969 + 3 ^ 40 * 1707359 * 2
def baseEnd_1707359 : Nat := 876695816779890683760505

theorem tailTrace_1707359 : CollatzResearch.WordTrace tailWord_1707359 prefixEnd_1707359 876695816779890683760505 := by
  unfold tailWord_1707359
  simp only [CollatzResearch.WordTrace]
  refine ⟨62272498621537411547349131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41514999081024941031566087 62272498621537411547349131)
  ·
    refine ⟨93408747932306117321023697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62272498621537411547349131 93408747932306117321023697)
    ·
      refine ⟨70056560949229587990767773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93408747932306117321023697 70056560949229587990767773)
      ·
        refine ⟨26271210355961095496537915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70056560949229587990767773 26271210355961095496537915)
        ·
          refine ⟨39406815533941643244806873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26271210355961095496537915 39406815533941643244806873)
          ·
            refine ⟨29555111650456232433605155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39406815533941643244806873 29555111650456232433605155)
            ·
              refine ⟨44332667475684348650407733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29555111650456232433605155 44332667475684348650407733)
              ·
                refine ⟨4156187575845407685975725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44332667475684348650407733 4156187575845407685975725)
                ·
                  refine ⟨1558570340942027882240897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4156187575845407685975725 1558570340942027882240897)
                  ·
                    refine ⟨1168927755706520911680673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558570340942027882240897 1168927755706520911680673)
                    ·
                      refine ⟨876695816779890683760505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168927755706520911680673 876695816779890683760505)
                      ·
                        rfl

theorem cell23_1707359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_1707359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707359 prefixEnd_1707359 := by exact prefixLift 1707359
  have htrace : WordTrace (prefixWord ++ tailWord_1707359) baseStart_1707359 baseEnd_1707359 := by
    simpa [prefixWord, tailWord_1707359, baseEnd_1707359] using wordTrace_append hprefix tailTrace_1707359
  have hstable : (prefixWord ++ tailWord_1707359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707359).length < 2 ^ (prefixWord ++ tailWord_1707359).sum := by decide
  have hdescent : baseEnd_1707359 < baseStart_1707359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707362 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1707362 : Nat := 118140960795 + 1707362 * 2 ^ 59
def prefixEnd_1707362 : Nat := 4983230072969 + 3 ^ 40 * 1707362 * 2
def baseEnd_1707362 : Nat := 876697357221854172022991

theorem tailTrace_1707362 : CollatzResearch.WordTrace tailWord_1707362 prefixEnd_1707362 876697357221854172022991 := by
  unfold tailWord_1707362
  simp only [CollatzResearch.WordTrace]
  refine ⟨15568152010131635764927085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41515072027017695373138893 15568152010131635764927085)
  ·
    refine ⟨5838057003799363411847657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15568152010131635764927085 5838057003799363411847657)
    ·
      refine ⟨4378542752849522558885743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5838057003799363411847657 4378542752849522558885743)
      ·
        refine ⟨6567814129274283838328615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378542752849522558885743 6567814129274283838328615)
        ·
          refine ⟨9851721193911425757492923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567814129274283838328615 9851721193911425757492923)
          ·
            refine ⟨14777581790867138636239385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9851721193911425757492923 14777581790867138636239385)
            ·
              refine ⟨11083186343150353977179539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14777581790867138636239385 11083186343150353977179539)
              ·
                refine ⟨16624779514725530965769309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083186343150353977179539 16624779514725530965769309)
                ·
                  refine ⟨6234292318022074112163491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16624779514725530965769309 6234292318022074112163491)
                  ·
                    refine ⟨9351438477033111168245237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6234292318022074112163491 9351438477033111168245237)
                    ·
                      refine ⟨876697357221854172022991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9351438477033111168245237 876697357221854172022991)
                      ·
                        rfl

theorem cell23_1707362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1707362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707362 prefixEnd_1707362 := by exact prefixLift 1707362
  have htrace : WordTrace (prefixWord ++ tailWord_1707362) baseStart_1707362 baseEnd_1707362 := by
    simpa [prefixWord, tailWord_1707362, baseEnd_1707362] using wordTrace_append hprefix tailTrace_1707362
  have hstable : (prefixWord ++ tailWord_1707362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707362).length < 2 ^ (prefixWord ++ tailWord_1707362).sum := by decide
  have hdescent : baseEnd_1707362 < baseStart_1707362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707372 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_1707372 : Nat := 118140960795 + 1707372 * 2 ^ 59
def prefixEnd_1707372 : Nat := 4983230072969 + 3 ^ 40 * 1707372 * 2
def baseEnd_1707372 : Nat := 876702492028399132897945

theorem tailTrace_1707372 : CollatzResearch.WordTrace tailWord_1707372 prefixEnd_1707372 876702492028399132897945 := by
  unfold tailWord_1707372
  simp only [CollatzResearch.WordTrace]
  refine ⟨31136486385245157383786185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41515315180326876511714913 31136486385245157383786185)
  ·
    refine ⟨23352364788933868037839639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31136486385245157383786185 23352364788933868037839639)
    ·
      refine ⟨35028547183400802056759459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23352364788933868037839639 35028547183400802056759459)
      ·
        refine ⟨52542820775101203085139189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35028547183400802056759459 52542820775101203085139189)
        ·
          refine ⟨4925889447665737789231799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52542820775101203085139189 4925889447665737789231799)
          ·
            refine ⟨7388834171498606683847699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925889447665737789231799 7388834171498606683847699)
            ·
              refine ⟨11083251257247910025771549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388834171498606683847699 11083251257247910025771549)
              ·
                refine ⟨4156219221467966259664331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11083251257247910025771549 4156219221467966259664331)
                ·
                  refine ⟨6234328832201949389496497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156219221467966259664331 6234328832201949389496497)
                  ·
                    refine ⟨4675746624151462042122373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6234328832201949389496497 4675746624151462042122373)
                    ·
                      refine ⟨876702492028399132897945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4675746624151462042122373 876702492028399132897945)
                      ·
                        rfl

theorem cell23_1707372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_1707372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707372 prefixEnd_1707372 := by exact prefixLift 1707372
  have htrace : WordTrace (prefixWord ++ tailWord_1707372) baseStart_1707372 baseEnd_1707372 := by
    simpa [prefixWord, tailWord_1707372, baseEnd_1707372] using wordTrace_append hprefix tailTrace_1707372
  have hstable : (prefixWord ++ tailWord_1707372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707372).length < 2 ^ (prefixWord ++ tailWord_1707372).sum := by decide
  have hdescent : baseEnd_1707372 < baseStart_1707372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707390 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1707390 : Nat := 118140960795 + 1707390 * 2 ^ 59
def prefixEnd_1707390 : Nat := 4983230072969 + 3 ^ 40 * 1707390 * 2
def baseEnd_1707390 : Nat := 292237244893393354157621

theorem tailTrace_1707390 : CollatzResearch.WordTrace tailWord_1707390 prefixEnd_1707390 292237244893393354157621 := by
  unfold tailWord_1707390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784203660553137980215953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41515752856283402561151749 7784203660553137980215953)
  ·
    refine ⟨5838152745414853485161965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7784203660553137980215953 5838152745414853485161965)
    ·
      refine ⟨2189307279530570056935737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5838152745414853485161965 2189307279530570056935737)
      ·
        refine ⟨1641980459647927542701803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189307279530570056935737 1641980459647927542701803)
        ·
          refine ⟨2462970689471891314052705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641980459647927542701803 2462970689471891314052705)
          ·
            refine ⟨1847228017103918485539529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462970689471891314052705 1847228017103918485539529)
            ·
              refine ⟨1385421012827938864154647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847228017103918485539529 1385421012827938864154647)
              ·
                refine ⟨2078131519241908296231971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385421012827938864154647 2078131519241908296231971)
                ·
                  refine ⟨3117197278862862444347957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078131519241908296231971 3117197278862862444347957)
                  ·
                    refine ⟨292237244893393354157621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3117197278862862444347957 292237244893393354157621)
                    ·
                      rfl

theorem cell23_1707390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1707390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707390 prefixEnd_1707390 := by exact prefixLift 1707390
  have htrace : WordTrace (prefixWord ++ tailWord_1707390) baseStart_1707390 baseEnd_1707390 := by
    simpa [prefixWord, tailWord_1707390, baseEnd_1707390] using wordTrace_append hprefix tailTrace_1707390
  have hstable : (prefixWord ++ tailWord_1707390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707390).length < 2 ^ (prefixWord ++ tailWord_1707390).sum := by decide
  have hdescent : baseEnd_1707390 < baseStart_1707390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707393 : List Nat := [1, 2, 4, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_1707393 : Nat := 118140960795 + 1707393 * 2 ^ 59
def prefixEnd_1707393 : Nat := 4983230072969 + 3 ^ 40 * 1707393 * 2
def baseEnd_1707393 : Nat := 876713275122143550735349

theorem tailTrace_1707393 : CollatzResearch.WordTrace tailWord_1707393 prefixEnd_1707393 876713275122143550735349 := by
  unfold tailWord_1707393
  simp only [CollatzResearch.WordTrace]
  refine ⟨62273738703414235354086833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41515825802276156902724555 62273738703414235354086833)
  ·
    refine ⟨46705304027560676515565125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62273738703414235354086833 46705304027560676515565125)
    ·
      refine ⟨8757244505167626846668461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46705304027560676515565125 8757244505167626846668461)
      ·
        refine ⟨3283966689437860067500673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8757244505167626846668461 3283966689437860067500673)
        ·
          refine ⟨2462975017078395050625505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3283966689437860067500673 2462975017078395050625505)
          ·
            refine ⟨1847231262808796287969129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462975017078395050625505 1847231262808796287969129)
            ·
              refine ⟨1385423447106597215976847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847231262808796287969129 1385423447106597215976847)
              ·
                refine ⟨2078135170659895823965271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385423447106597215976847 2078135170659895823965271)
                ·
                  refine ⟨3117202755989843735947907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078135170659895823965271 3117202755989843735947907)
                  ·
                    refine ⟨4675804133984765603921861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3117202755989843735947907 4675804133984765603921861)
                    ·
                      refine ⟨876713275122143550735349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4675804133984765603921861 876713275122143550735349)
                      ·
                        rfl

theorem cell23_1707393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_1707393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707393 prefixEnd_1707393 := by exact prefixLift 1707393
  have htrace : WordTrace (prefixWord ++ tailWord_1707393) baseStart_1707393 baseEnd_1707393 := by
    simpa [prefixWord, tailWord_1707393, baseEnd_1707393] using wordTrace_append hprefix tailTrace_1707393
  have hstable : (prefixWord ++ tailWord_1707393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707393).length < 2 ^ (prefixWord ++ tailWord_1707393).sum := by decide
  have hdescent : baseEnd_1707393 < baseStart_1707393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707396 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_1707396 : Nat := 118140960795 + 1707396 * 2 ^ 59
def prefixEnd_1707396 : Nat := 4983230072969 + 3 ^ 40 * 1707396 * 2
def baseEnd_1707396 : Nat := 876714815564107038997835

theorem tailTrace_1707396 : CollatzResearch.WordTrace tailWord_1707396 prefixEnd_1707396 876714815564107038997835 := by
  unfold tailWord_1707396
  simp only [CollatzResearch.WordTrace]
  refine ⟨31136924061201683433223021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41515898748268911244297361 31136924061201683433223021)
  ·
    refine ⟨11676346522950631287458633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31136924061201683433223021 11676346522950631287458633)
    ·
      refine ⟨8757259892212973465593975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11676346522950631287458633 8757259892212973465593975)
      ·
        refine ⟨13135889838319460198390963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8757259892212973465593975 13135889838319460198390963)
        ·
          refine ⟨19703834757479190297586445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13135889838319460198390963 19703834757479190297586445)
          ·
            refine ⟨7388938034054696361594917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19703834757479190297586445 7388938034054696361594917)
            ·
              refine ⟨1385425881385255567799047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7388938034054696361594917 1385425881385255567799047)
              ·
                refine ⟨2078138822077883351698571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385425881385255567799047 2078138822077883351698571)
                ·
                  refine ⟨3117208233116825027547857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078138822077883351698571 3117208233116825027547857)
                  ·
                    refine ⟨2337906174837618770660893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3117208233116825027547857 2337906174837618770660893)
                    ·
                      refine ⟨876714815564107038997835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337906174837618770660893 876714815564107038997835)
                      ·
                        rfl

theorem cell23_1707396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_1707396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707396 prefixEnd_1707396 := by exact prefixLift 1707396
  have htrace : WordTrace (prefixWord ++ tailWord_1707396) baseStart_1707396 baseEnd_1707396 := by
    simpa [prefixWord, tailWord_1707396, baseEnd_1707396] using wordTrace_append hprefix tailTrace_1707396
  have hstable : (prefixWord ++ tailWord_1707396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707396).length < 2 ^ (prefixWord ++ tailWord_1707396).sum := by decide
  have hdescent : baseEnd_1707396 < baseStart_1707396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707410 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1707410 : Nat := 118140960795 + 1707410 * 2 ^ 59
def prefixEnd_1707410 : Nat := 4983230072969 + 3 ^ 40 * 1707410 * 2
def baseEnd_1707410 : Nat := 876722004293269984222771

theorem tailTrace_1707410 : CollatzResearch.WordTrace tailWord_1707410 prefixEnd_1707410 876722004293269984222771 := by
  unfold tailWord_1707410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15568589686088161814363921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41516239162901764838303789 15568589686088161814363921)
  ·
    refine ⟨11676442264566121360772941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15568589686088161814363921 11676442264566121360772941)
    ·
      refine ⟨4378665849212295510289853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11676442264566121360772941 4378665849212295510289853)
      ·
        refine ⟨1641999693454610816358695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4378665849212295510289853 1641999693454610816358695)
        ·
          refine ⟨2462999540181916224538043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641999693454610816358695 2462999540181916224538043)
          ·
            refine ⟨3694499310272874336807065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462999540181916224538043 3694499310272874336807065)
            ·
              refine ⟨2770874482704655752605299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3694499310272874336807065 2770874482704655752605299)
              ·
                refine ⟨4156311724056983628907949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770874482704655752605299 4156311724056983628907949)
                ·
                  refine ⟨1558616896521368860840481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4156311724056983628907949 1558616896521368860840481)
                  ·
                    refine ⟨1168962672391026645630361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558616896521368860840481 1168962672391026645630361)
                    ·
                      refine ⟨876722004293269984222771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1168962672391026645630361 876722004293269984222771)
                      ·
                        rfl

theorem cell23_1707410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1707410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707410 prefixEnd_1707410 := by exact prefixLift 1707410
  have htrace : WordTrace (prefixWord ++ tailWord_1707410) baseStart_1707410 baseEnd_1707410 := by
    simpa [prefixWord, tailWord_1707410, baseEnd_1707410] using wordTrace_append hprefix tailTrace_1707410
  have hstable : (prefixWord ++ tailWord_1707410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707410).length < 2 ^ (prefixWord ++ tailWord_1707410).sum := by decide
  have hdescent : baseEnd_1707410 < baseStart_1707410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707426 : List Nat := [3, 3, 1, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_1707426 : Nat := 118140960795 + 1707426 * 2 ^ 59
def prefixEnd_1707426 : Nat := 4983230072969 + 3 ^ 40 * 1707426 * 2
def baseEnd_1707426 : Nat := 876730219983741921622697

theorem tailTrace_1707426 : CollatzResearch.WordTrace tailWord_1707426 prefixEnd_1707426 876730219983741921622697 := by
  unfold tailWord_1707426
  simp only [CollatzResearch.WordTrace]
  refine ⟨15568735578073670497509533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41516628208196454660025421 15568735578073670497509533)
  ·
    refine ⟨5838275841777626436566075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15568735578073670497509533 5838275841777626436566075)
    ·
      refine ⟨8757413762666439654849113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5838275841777626436566075 8757413762666439654849113)
      ·
        refine ⟨6568060321999829741136835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8757413762666439654849113 6568060321999829741136835)
        ·
          refine ⟨9852090482999744611705253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568060321999829741136835 9852090482999744611705253)
          ·
            refine ⟨1847266965562452114694735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9852090482999744611705253 1847266965562452114694735)
            ·
              refine ⟨2770900448343678172042103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847266965562452114694735 2770900448343678172042103)
              ·
                refine ⟨4156350672515517258063155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770900448343678172042103 4156350672515517258063155)
                ·
                  refine ⟨6234526008773275887094733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156350672515517258063155 6234526008773275887094733)
                  ·
                    refine ⟨2337947253289978457660525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6234526008773275887094733 2337947253289978457660525)
                    ·
                      refine ⟨876730219983741921622697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2337947253289978457660525 876730219983741921622697)
                      ·
                        rfl

theorem cell23_1707426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_1707426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707426 prefixEnd_1707426 := by exact prefixLift 1707426
  have htrace : WordTrace (prefixWord ++ tailWord_1707426) baseStart_1707426 baseEnd_1707426 := by
    simpa [prefixWord, tailWord_1707426, baseEnd_1707426] using wordTrace_append hprefix tailTrace_1707426
  have hstable : (prefixWord ++ tailWord_1707426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707426).length < 2 ^ (prefixWord ++ tailWord_1707426).sum := by decide
  have hdescent : baseEnd_1707426 < baseStart_1707426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707455 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 9]
def baseStart_1707455 : Nat := 118140960795 + 1707455 * 2 ^ 59
def prefixEnd_1707455 : Nat := 4983230072969 + 3 ^ 40 * 1707455 * 2
def baseEnd_1707455 : Nat := 97416123435858034240007

theorem tailTrace_1707455 : CollatzResearch.WordTrace tailWord_1707455 prefixEnd_1707455 97416123435858034240007 := by
  unfold tailWord_1707455
  simp only [CollatzResearch.WordTrace]
  refine ⟨62276000029189619942843819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41517333352793079961895879 62276000029189619942843819)
  ·
    refine ⟨93414000043784429914265729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62276000029189619942843819 93414000043784429914265729)
    ·
      refine ⟨70060500032838322435699297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93414000043784429914265729 70060500032838322435699297)
      ·
        refine ⟨52545375024628741826774473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70060500032838322435699297 52545375024628741826774473)
        ·
          refine ⟨39409031268471556370080855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52545375024628741826774473 39409031268471556370080855)
          ·
            refine ⟨59113546902707334555121283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39409031268471556370080855 59113546902707334555121283)
            ·
              refine ⟨88670320354061001832681925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59113546902707334555121283 88670320354061001832681925)
              ·
                refine ⟨16625685066386437843627861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88670320354061001832681925 16625685066386437843627861)
                ·
                  refine ⟨97416123435858034240007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16625685066386437843627861 97416123435858034240007)
                  ·
                    rfl

theorem cell23_1707455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 9].length) (baseStart_1707455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707455 prefixEnd_1707455 := by exact prefixLift 1707455
  have htrace : WordTrace (prefixWord ++ tailWord_1707455) baseStart_1707455 baseEnd_1707455 := by
    simpa [prefixWord, tailWord_1707455, baseEnd_1707455] using wordTrace_append hprefix tailTrace_1707455
  have hstable : (prefixWord ++ tailWord_1707455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707455).length < 2 ^ (prefixWord ++ tailWord_1707455).sum := by decide
  have hdescent : baseEnd_1707455 < baseStart_1707455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707465 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_1707465 : Nat := 118140960795 + 1707465 * 2 ^ 59
def prefixEnd_1707465 : Nat := 4983230072969 + 3 ^ 40 * 1707465 * 2
def baseEnd_1707465 : Nat := 876750245729267269035017

theorem tailTrace_1707465 : CollatzResearch.WordTrace tailWord_1707465 prefixEnd_1707465 876750245729267269035017 := by
  unfold tailWord_1707465
  simp only [CollatzResearch.WordTrace]
  refine ⟨62276364759153391650707849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41517576506102261100471899 62276364759153391650707849)
  ·
    refine ⟨46707273569365043738030887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62276364759153391650707849 46707273569365043738030887)
    ·
      refine ⟨70060910354047565607046331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46707273569365043738030887 70060910354047565607046331)
      ·
        refine ⟨105091365531071348410569497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70060910354047565607046331 105091365531071348410569497)
        ·
          refine ⟨78818524148303511307927123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105091365531071348410569497 78818524148303511307927123)
          ·
            refine ⟨118227786222455266961890685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78818524148303511307927123 118227786222455266961890685)
            ·
              refine ⟨44335419833420725110709007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118227786222455266961890685 44335419833420725110709007)
              ·
                refine ⟨66503129750131087666063511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44335419833420725110709007 66503129750131087666063511)
                ·
                  refine ⟨99754694625196631499095267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66503129750131087666063511 99754694625196631499095267)
                  ·
                    refine ⟨149632041937794947248642901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99754694625196631499095267 149632041937794947248642901)
                    ·
                      refine ⟨876750245729267269035017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 149632041937794947248642901 876750245729267269035017)
                      ·
                        rfl

theorem cell23_1707465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_1707465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707465 prefixEnd_1707465 := by exact prefixLift 1707465
  have htrace : WordTrace (prefixWord ++ tailWord_1707465) baseStart_1707465 baseEnd_1707465 := by
    simpa [prefixWord, tailWord_1707465, baseEnd_1707465] using wordTrace_append hprefix tailTrace_1707465
  have hstable : (prefixWord ++ tailWord_1707465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707465).length < 2 ^ (prefixWord ++ tailWord_1707465).sum := by decide
  have hdescent : baseEnd_1707465 < baseStart_1707465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707466 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_1707466 : Nat := 118140960795 + 1707466 * 2 ^ 59
def prefixEnd_1707466 : Nat := 4983230072969 + 3 ^ 40 * 1707466 * 2
def baseEnd_1707466 : Nat := 876750759209921765122513

theorem tailTrace_1707466 : CollatzResearch.WordTrace tailWord_1707466 prefixEnd_1707466 876750759209921765122513 := by
  unfold tailWord_1707466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15569100308037442205373563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41517600821433179214329501 15569100308037442205373563)
  ·
    refine ⟨23353650462056163308060345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15569100308037442205373563 23353650462056163308060345)
    ·
      refine ⟨17515237846542122481045259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23353650462056163308060345 17515237846542122481045259)
      ·
        refine ⟨26272856769813183721567889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17515237846542122481045259 26272856769813183721567889)
        ·
          refine ⟨19704642577359887791175917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26272856769813183721567889 19704642577359887791175917)
          ·
            refine ⟨7389240966509957921690969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19704642577359887791175917 7389240966509957921690969)
            ·
              refine ⟨5541930724882468441268227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389240966509957921690969 5541930724882468441268227)
              ·
                refine ⟨8312896087323702661902341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541930724882468441268227 8312896087323702661902341)
                ·
                  refine ⟨1558668016373194249106689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8312896087323702661902341 1558668016373194249106689)
                  ·
                    refine ⟨1169001012279895686830017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558668016373194249106689 1169001012279895686830017)
                    ·
                      refine ⟨876750759209921765122513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169001012279895686830017 876750759209921765122513)
                      ·
                        rfl

theorem cell23_1707466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_1707466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707466 prefixEnd_1707466 := by exact prefixLift 1707466
  have htrace : WordTrace (prefixWord ++ tailWord_1707466) baseStart_1707466 baseEnd_1707466 := by
    simpa [prefixWord, tailWord_1707466, baseEnd_1707466] using wordTrace_append hprefix tailTrace_1707466
  have hstable : (prefixWord ++ tailWord_1707466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707466).length < 2 ^ (prefixWord ++ tailWord_1707466).sum := by decide
  have hdescent : baseEnd_1707466 < baseStart_1707466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707512 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_1707512 : Nat := 118140960795 + 1707512 * 2 ^ 59
def prefixEnd_1707512 : Nat := 4983230072969 + 3 ^ 40 * 1707512 * 2
def baseEnd_1707512 : Nat := 876774379320028585147301

theorem tailTrace_1707512 : CollatzResearch.WordTrace tailWord_1707512 prefixEnd_1707512 876774379320028585147301 := by
  unfold tailWord_1707512
  simp only [CollatzResearch.WordTrace]
  refine ⟨31139039494991559338834395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41518719326655412451779193 31139039494991559338834395)
  ·
    refine ⟨46708559242487339008251593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31139039494991559338834395 46708559242487339008251593)
    ·
      refine ⟨35031419431865504256188695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46708559242487339008251593 35031419431865504256188695)
      ·
        refine ⟨52547129147798256384283043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35031419431865504256188695 52547129147798256384283043)
        ·
          refine ⟨78820693721697384576424565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52547129147798256384283043 78820693721697384576424565)
          ·
            refine ⟨7389440036409129804039803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78820693721697384576424565 7389440036409129804039803)
            ·
              refine ⟨11084160054613694706059705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7389440036409129804039803 11084160054613694706059705)
              ·
                refine ⟨8313120040960271029544779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11084160054613694706059705 8313120040960271029544779)
                ·
                  refine ⟨12469680061440406544317169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313120040960271029544779 12469680061440406544317169)
                  ·
                    refine ⟨9352260046080304908237877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12469680061440406544317169 9352260046080304908237877)
                    ·
                      refine ⟨876774379320028585147301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9352260046080304908237877 876774379320028585147301)
                      ·
                        rfl

theorem cell23_1707512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_1707512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707512 prefixEnd_1707512 := by exact prefixLift 1707512
  have htrace : WordTrace (prefixWord ++ tailWord_1707512) baseStart_1707512 baseEnd_1707512 := by
    simpa [prefixWord, tailWord_1707512, baseEnd_1707512] using wordTrace_append hprefix tailTrace_1707512
  have hstable : (prefixWord ++ tailWord_1707512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707512).length < 2 ^ (prefixWord ++ tailWord_1707512).sum := by decide
  have hdescent : baseEnd_1707512 < baseStart_1707512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707539 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 6, 2]
def baseStart_1707539 : Nat := 118140960795 + 1707539 * 2 ^ 59
def prefixEnd_1707539 : Nat := 4983230072969 + 3 ^ 40 * 1707539 * 2
def baseEnd_1707539 : Nat := 876788243297699979509677

theorem tailTrace_1707539 : CollatzResearch.WordTrace tailWord_1707539 prefixEnd_1707539 876788243297699979509677 := by
  unfold tailWord_1707539
  simp only [CollatzResearch.WordTrace]
  refine ⟨62279063760885302288901671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41519375840590201525934447 62279063760885302288901671)
  ·
    refine ⟨93418595641327953433352507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62279063760885302288901671 93418595641327953433352507)
    ·
      refine ⟨140127893461991930150028761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93418595641327953433352507 140127893461991930150028761)
      ·
        refine ⟨105095920096493947612521571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140127893461991930150028761 105095920096493947612521571)
        ·
          refine ⟨157643880144740921418782357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105095920096493947612521571 157643880144740921418782357)
          ·
            refine ⟨7389556881784730691505423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157643880144740921418782357 7389556881784730691505423)
            ·
              refine ⟨11084335322677096037258135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7389556881784730691505423 11084335322677096037258135)
              ·
                refine ⟨16626502984015644055887203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11084335322677096037258135 16626502984015644055887203)
                ·
                  refine ⟨24939754476023466083830805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16626502984015644055887203 24939754476023466083830805)
                  ·
                    refine ⟨1169050991063599972679569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24939754476023466083830805 1169050991063599972679569)
                    ·
                      refine ⟨876788243297699979509677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169050991063599972679569 876788243297699979509677)
                      ·
                        rfl

theorem cell23_1707539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 6, 2].length) (baseStart_1707539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707539 prefixEnd_1707539 := by exact prefixLift 1707539
  have htrace : WordTrace (prefixWord ++ tailWord_1707539) baseStart_1707539 baseEnd_1707539 := by
    simpa [prefixWord, tailWord_1707539, baseEnd_1707539] using wordTrace_append hprefix tailTrace_1707539
  have hstable : (prefixWord ++ tailWord_1707539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707539).length < 2 ^ (prefixWord ++ tailWord_1707539).sum := by decide
  have hdescent : baseEnd_1707539 < baseStart_1707539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707596 : List Nat := [2, 2, 1, 3, 1, 4, 3, 1, 6]
def baseStart_1707596 : Nat := 118140960795 + 1707596 * 2 ^ 59
def prefixEnd_1707596 : Nat := 4983230072969 + 3 ^ 40 * 1707596 * 2
def baseEnd_1707596 : Nat := 97424167966111806277435

theorem tailTrace_1707596 : CollatzResearch.WordTrace tailWord_1707596 prefixEnd_1707596 97424167966111806277435 := by
  unfold tailWord_1707596
  simp only [CollatzResearch.WordTrace]
  refine ⟨31140571360839400511863321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41520761814452534015817761 31140571360839400511863321)
  ·
    refine ⟨23355428520629550383897491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31140571360839400511863321 23355428520629550383897491)
    ·
      refine ⟨35033142780944325575846237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23355428520629550383897491 35033142780944325575846237)
      ·
        refine ⟨13137428542854122090942339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35033142780944325575846237 13137428542854122090942339)
        ·
          refine ⟨19706142814281183136413509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13137428542854122090942339 19706142814281183136413509)
          ·
            refine ⟨3694901777677721838077533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19706142814281183136413509 3694901777677721838077533)
            ·
              refine ⟨1385588166629145689279075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3694901777677721838077533 1385588166629145689279075)
              ·
                refine ⟨2078382249943718533918613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385588166629145689279075 2078382249943718533918613)
                ·
                  refine ⟨97424167966111806277435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2078382249943718533918613 97424167966111806277435)
                  ·
                    rfl

theorem cell23_1707596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_1707596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707596 prefixEnd_1707596 := by exact prefixLift 1707596
  have htrace : WordTrace (prefixWord ++ tailWord_1707596) baseStart_1707596 baseEnd_1707596 := by
    simpa [prefixWord, tailWord_1707596, baseEnd_1707596] using wordTrace_append hprefix tailTrace_1707596
  have hstable : (prefixWord ++ tailWord_1707596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707596).length < 2 ^ (prefixWord ++ tailWord_1707596).sum := by decide
  have hdescent : baseEnd_1707596 < baseStart_1707596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707616 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 2, 3, 2]
def baseStart_1707616 : Nat := 118140960795 + 1707616 * 2 ^ 59
def prefixEnd_1707616 : Nat := 4983230072969 + 3 ^ 40 * 1707616 * 2
def baseEnd_1707616 : Nat := 876827781308096178246823

theorem tailTrace_1707616 : CollatzResearch.WordTrace tailWord_1707616 prefixEnd_1707616 876827781308096178246823 := by
  unfold tailWord_1707616
  simp only [CollatzResearch.WordTrace]
  refine ⟨31140936090803172219727351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41521248121070896292969801 31140936090803172219727351)
  ·
    refine ⟨46711404136204758329591027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31140936090803172219727351 46711404136204758329591027)
    ·
      refine ⟨70067106204307137494386541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46711404136204758329591027 70067106204307137494386541)
      ·
        refine ⟨26275164826615176560394953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70067106204307137494386541 26275164826615176560394953)
        ·
          refine ⟨19706373619961382420296215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26275164826615176560394953 19706373619961382420296215)
          ·
            refine ⟨29559560429942073630444323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19706373619961382420296215 29559560429942073630444323)
            ·
              refine ⟨44339340644913110445666485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29559560429942073630444323 44339340644913110445666485)
              ·
                refine ⟨4156813185460604104281233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44339340644913110445666485 4156813185460604104281233)
                ·
                  refine ⟨3117609889095453078210925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156813185460604104281233 3117609889095453078210925)
                  ·
                    refine ⟨1169103708410794904329097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117609889095453078210925 1169103708410794904329097)
                    ·
                      refine ⟨876827781308096178246823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169103708410794904329097 876827781308096178246823)
                      ·
                        rfl

theorem cell23_1707616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_1707616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707616 prefixEnd_1707616 := by exact prefixLift 1707616
  have htrace : WordTrace (prefixWord ++ tailWord_1707616) baseStart_1707616 baseEnd_1707616 := by
    simpa [prefixWord, tailWord_1707616, baseEnd_1707616] using wordTrace_append hprefix tailTrace_1707616
  have hstable : (prefixWord ++ tailWord_1707616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707616).length < 2 ^ (prefixWord ++ tailWord_1707616).sum := by decide
  have hdescent : baseEnd_1707616 < baseStart_1707616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707626 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1707626 : Nat := 118140960795 + 1707626 * 2 ^ 59
def prefixEnd_1707626 : Nat := 4983230072969 + 3 ^ 40 * 1707626 * 2
def baseEnd_1707626 : Nat := 292277638704880379707259

theorem tailTrace_1707626 : CollatzResearch.WordTrace tailWord_1707626 prefixEnd_1707626 292277638704880379707259 := by
  unfold tailWord_1707626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15570559227892529036829683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41521491274380077431545821 15570559227892529036829683)
  ·
    refine ⟨23355838841838793555244525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15570559227892529036829683 23355838841838793555244525)
    ·
      refine ⟨8758439565689547583216697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23355838841838793555244525 8758439565689547583216697)
      ·
        refine ⟨6568829674267160687412523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8758439565689547583216697 6568829674267160687412523)
        ·
          refine ⟨9853244511400741031118785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568829674267160687412523 9853244511400741031118785)
          ·
            refine ⟨7389933383550555773339089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9853244511400741031118785 7389933383550555773339089)
            ·
              refine ⟨5542450037662916830004317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389933383550555773339089 5542450037662916830004317)
              ·
                refine ⟨2078418764123593811251619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5542450037662916830004317 2078418764123593811251619)
                ·
                  refine ⟨3117628146185390716877429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078418764123593811251619 3117628146185390716877429)
                  ·
                    refine ⟨292277638704880379707259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3117628146185390716877429 292277638704880379707259)
                    ·
                      rfl

theorem cell23_1707626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1707626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707626 prefixEnd_1707626 := by exact prefixLift 1707626
  have htrace : WordTrace (prefixWord ++ tailWord_1707626) baseStart_1707626 baseEnd_1707626 := by
    simpa [prefixWord, tailWord_1707626, baseEnd_1707626] using wordTrace_append hprefix tailTrace_1707626
  have hstable : (prefixWord ++ tailWord_1707626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707626).length < 2 ^ (prefixWord ++ tailWord_1707626).sum := by decide
  have hdescent : baseEnd_1707626 < baseStart_1707626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707659 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4]
def baseStart_1707659 : Nat := 118140960795 + 1707659 * 2 ^ 59
def prefixEnd_1707659 : Nat := 4983230072969 + 3 ^ 40 * 1707659 * 2
def baseEnd_1707659 : Nat := 876849860976239510009125

theorem tailTrace_1707659 : CollatzResearch.WordTrace tailWord_1707659 prefixEnd_1707659 876849860976239510009125 := by
  unfold tailWord_1707659
  simp only [CollatzResearch.WordTrace]
  refine ⟨62283440520450562783270031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41522293680300375188846687 62283440520450562783270031)
  ·
    refine ⟨93425160780675844174905047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62283440520450562783270031 93425160780675844174905047)
    ·
      refine ⟨140137741171013766262357571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93425160780675844174905047 140137741171013766262357571)
      ·
        refine ⟨210206611756520649393536357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140137741171013766262357571 210206611756520649393536357)
        ·
          refine ⟨39413739704347621761288067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210206611756520649393536357 39413739704347621761288067)
          ·
            refine ⟨59120609556521432641932101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39413739704347621761288067 59120609556521432641932101)
            ·
              refine ⟨11085114291847768620362269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59120609556521432641932101 11085114291847768620362269)
              ·
                refine ⟨4156917859442913232635851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11085114291847768620362269 4156917859442913232635851)
                ·
                  refine ⟨6235376789164369848953777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156917859442913232635851 6235376789164369848953777)
                  ·
                    refine ⟨4676532591873277386715333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6235376789164369848953777 4676532591873277386715333)
                    ·
                      refine ⟨876849860976239510009125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4676532591873277386715333 876849860976239510009125)
                      ·
                        rfl

theorem cell23_1707659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].length) (baseStart_1707659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707659 prefixEnd_1707659 := by exact prefixLift 1707659
  have htrace : WordTrace (prefixWord ++ tailWord_1707659) baseStart_1707659 baseEnd_1707659 := by
    simpa [prefixWord, tailWord_1707659, baseEnd_1707659] using wordTrace_append hprefix tailTrace_1707659
  have hstable : (prefixWord ++ tailWord_1707659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707659).length < 2 ^ (prefixWord ++ tailWord_1707659).sum := by decide
  have hdescent : baseEnd_1707659 < baseStart_1707659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707683 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 1, 2, 3]
def baseStart_1707683 : Nat := 118140960795 + 1707683 * 2 ^ 59
def prefixEnd_1707683 : Nat := 4983230072969 + 3 ^ 40 * 1707683 * 2
def baseEnd_1707683 : Nat := 876862184511947416109015

theorem tailTrace_1707683 : CollatzResearch.WordTrace tailWord_1707683 prefixEnd_1707683 876862184511947416109015 := by
  unfold tailWord_1707683
  simp only [CollatzResearch.WordTrace]
  refine ⟨62284315872363614882143703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41522877248242409921429135 62284315872363614882143703)
  ·
    refine ⟨93426473808545422323215555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62284315872363614882143703 93426473808545422323215555)
    ·
      refine ⟨140139710712818133484823333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93426473808545422323215555 140139710712818133484823333)
      ·
        refine ⟨26276195758653400028404375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140139710712818133484823333 26276195758653400028404375)
        ·
          refine ⟨39414293637980100042606563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26276195758653400028404375 39414293637980100042606563)
          ·
            refine ⟨59121440456970150063909845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39414293637980100042606563 59121440456970150063909845)
            ·
              refine ⟨1385658760710237892122887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59121440456970150063909845 1385658760710237892122887)
              ·
                refine ⟨2078488141065356838184331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385658760710237892122887 2078488141065356838184331)
                ·
                  refine ⟨3117732211598035257276497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078488141065356838184331 3117732211598035257276497)
                  ·
                    refine ⟨2338299158698526442957373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3117732211598035257276497 2338299158698526442957373)
                    ·
                      refine ⟨876862184511947416109015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2338299158698526442957373 876862184511947416109015)
                      ·
                        rfl

theorem cell23_1707683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_1707683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707683 prefixEnd_1707683 := by exact prefixLift 1707683
  have htrace : WordTrace (prefixWord ++ tailWord_1707683) baseStart_1707683 baseEnd_1707683 := by
    simpa [prefixWord, tailWord_1707683, baseEnd_1707683] using wordTrace_append hprefix tailTrace_1707683
  have hstable : (prefixWord ++ tailWord_1707683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707683).length < 2 ^ (prefixWord ++ tailWord_1707683).sum := by decide
  have hdescent : baseEnd_1707683 < baseStart_1707683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707696 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 4, 1, 3]
def baseStart_1707696 : Nat := 118140960795 + 1707696 * 2 ^ 59
def prefixEnd_1707696 : Nat := 4983230072969 + 3 ^ 40 * 1707696 * 2
def baseEnd_1707696 : Nat := 876868859760455865246455

theorem tailTrace_1707696 : CollatzResearch.WordTrace tailWord_1707696 prefixEnd_1707696 876868859760455865246455 := by
  unfold tailWord_1707696
  simp only [CollatzResearch.WordTrace]
  refine ⟨31142395010658259051183471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41523193347544345401577961 31142395010658259051183471)
  ·
    refine ⟨46713592515987388576775207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31142395010658259051183471 46713592515987388576775207)
    ·
      refine ⟨70070388773981082865162811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46713592515987388576775207 70070388773981082865162811)
      ·
        refine ⟨105105583160971624297744217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70070388773981082865162811 105105583160971624297744217)
        ·
          refine ⟨78829187370728718223308163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105105583160971624297744217 78829187370728718223308163)
          ·
            refine ⟨118243781056093077334962245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78829187370728718223308163 118243781056093077334962245)
            ·
              refine ⟨22170708948017452000305421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118243781056093077334962245 22170708948017452000305421)
              ·
                refine ⟨8314015855506544500114533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22170708948017452000305421 8314015855506544500114533)
                ·
                  refine ⟨1558877972907477093771475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8314015855506544500114533 1558877972907477093771475)
                  ·
                    refine ⟨2338316959361215640657213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1558877972907477093771475 2338316959361215640657213)
                    ·
                      refine ⟨876868859760455865246455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2338316959361215640657213 876868859760455865246455)
                      ·
                        rfl

theorem cell23_1707696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_1707696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707696 prefixEnd_1707696 := by exact prefixLift 1707696
  have htrace : WordTrace (prefixWord ++ tailWord_1707696) baseStart_1707696 baseEnd_1707696 := by
    simpa [prefixWord, tailWord_1707696, baseEnd_1707696] using wordTrace_append hprefix tailTrace_1707696
  have hstable : (prefixWord ++ tailWord_1707696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707696).length < 2 ^ (prefixWord ++ tailWord_1707696).sum := by decide
  have hdescent : baseEnd_1707696 < baseStart_1707696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707719 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1707719 : Nat := 118140960795 + 1707719 * 2 ^ 59
def prefixEnd_1707719 : Nat := 4983230072969 + 3 ^ 40 * 1707719 * 2
def baseEnd_1707719 : Nat := 876880669815509275258849

theorem tailTrace_1707719 : CollatzResearch.WordTrace tailWord_1707719 prefixEnd_1707719 876880669815509275258849 := by
  unfold tailWord_1707719
  simp only [CollatzResearch.WordTrace]
  refine ⟨62285628900233193030454211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41523752600155462020302807 62285628900233193030454211)
  ·
    refine ⟨93428443350349789545681317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62285628900233193030454211 93428443350349789545681317)
    ·
      refine ⟨17517833128190585539815247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93428443350349789545681317 17517833128190585539815247)
      ·
        refine ⟨26276749692285878309722871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17517833128190585539815247 26276749692285878309722871)
        ·
          refine ⟨39415124538428817464584307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26276749692285878309722871 39415124538428817464584307)
          ·
            refine ⟨59122686807643226196876461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39415124538428817464584307 59122686807643226196876461)
            ·
              refine ⟨22171007552866209823828673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59122686807643226196876461 22171007552866209823828673)
              ·
                refine ⟨16628255664649657367871505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22171007552866209823828673 16628255664649657367871505)
                ·
                  refine ⟨12471191748487243025903629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16628255664649657367871505 12471191748487243025903629)
                  ·
                    refine ⟨4676696905682716134713861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12471191748487243025903629 4676696905682716134713861)
                    ·
                      refine ⟨876880669815509275258849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4676696905682716134713861 876880669815509275258849)
                      ·
                        rfl

theorem cell23_1707719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1707719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707719 prefixEnd_1707719 := by exact prefixLift 1707719
  have htrace : WordTrace (prefixWord ++ tailWord_1707719) baseStart_1707719 baseEnd_1707719 := by
    simpa [prefixWord, tailWord_1707719, baseEnd_1707719] using wordTrace_append hprefix tailTrace_1707719
  have hstable : (prefixWord ++ tailWord_1707719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707719).length < 2 ^ (prefixWord ++ tailWord_1707719).sum := by decide
  have hdescent : baseEnd_1707719 < baseStart_1707719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707747 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1707747 : Nat := 118140960795 + 1707747 * 2 ^ 59
def prefixEnd_1707747 : Nat := 4983230072969 + 3 ^ 40 * 1707747 * 2
def baseEnd_1707747 : Nat := 876895047273835165708721

theorem tailTrace_1707747 : CollatzResearch.WordTrace tailWord_1707747 prefixEnd_1707747 876895047273835165708721 := by
  unfold tailWord_1707747
  simp only [CollatzResearch.WordTrace]
  refine ⟨62286650144131753812473495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41524433429421169208315663 62286650144131753812473495)
  ·
    refine ⟨93429975216197630718710243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62286650144131753812473495 93429975216197630718710243)
    ·
      refine ⟨140144962824296446078065365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93429975216197630718710243 140144962824296446078065365)
      ·
        refine ⟨3284647566194447954954657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 140144962824296446078065365 3284647566194447954954657)
        ·
          refine ⟨2463485674645835966215993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3284647566194447954954657 2463485674645835966215993)
          ·
            refine ⟨1847614255984376974661995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463485674645835966215993 1847614255984376974661995)
            ·
              refine ⟨2771421383976565461992993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847614255984376974661995 2771421383976565461992993)
              ·
                refine ⟨2078566037982424096494745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2771421383976565461992993 2078566037982424096494745)
                ·
                  refine ⟨1558924528486818072371059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078566037982424096494745 1558924528486818072371059)
                  ·
                    refine ⟨2338386792730227108556589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1558924528486818072371059 2338386792730227108556589)
                    ·
                      refine ⟨876895047273835165708721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2338386792730227108556589 876895047273835165708721)
                      ·
                        rfl

theorem cell23_1707747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1707747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707747 prefixEnd_1707747 := by exact prefixLift 1707747
  have htrace : WordTrace (prefixWord ++ tailWord_1707747) baseStart_1707747 baseEnd_1707747 := by
    simpa [prefixWord, tailWord_1707747, baseEnd_1707747] using wordTrace_append hprefix tailTrace_1707747
  have hstable : (prefixWord ++ tailWord_1707747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707747).length < 2 ^ (prefixWord ++ tailWord_1707747).sum := by decide
  have hdescent : baseEnd_1707747 < baseStart_1707747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707782 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1707782 : Nat := 118140960795 + 1707782 * 2 ^ 59
def prefixEnd_1707782 : Nat := 4983230072969 + 3 ^ 40 * 1707782 * 2
def baseEnd_1707782 : Nat := 876913019096742528771061

theorem tailTrace_1707782 : CollatzResearch.WordTrace tailWord_1707782 prefixEnd_1707782 876913019096742528771061 := by
  unfold tailWord_1707782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1946497709343904837187425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41525284466003303193331733 1946497709343904837187425)
  ·
    refine ⟨1459873282007928627890569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1946497709343904837187425 1459873282007928627890569)
    ·
      refine ⟨1094904961505946470917927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1459873282007928627890569 1094904961505946470917927)
      ·
        refine ⟨1642357442258919706376891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094904961505946470917927 1642357442258919706376891)
        ·
          refine ⟨2463536163388379559565337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642357442258919706376891 2463536163388379559565337)
          ·
            refine ⟨1847652122541284669674003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463536163388379559565337 1847652122541284669674003)
            ·
              refine ⟨2771478183811927004511005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847652122541284669674003 2771478183811927004511005)
              ·
                refine ⟨1039304318929472626691627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2771478183811927004511005 1039304318929472626691627)
                ·
                  refine ⟨1558956478394208940037441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039304318929472626691627 1558956478394208940037441)
                  ·
                    refine ⟨1169217358795656705028081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1558956478394208940037441 1169217358795656705028081)
                    ·
                      refine ⟨876913019096742528771061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169217358795656705028081 876913019096742528771061)
                      ·
                        rfl

theorem cell23_1707782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1707782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707782 prefixEnd_1707782 := by exact prefixLift 1707782
  have htrace : WordTrace (prefixWord ++ tailWord_1707782) baseStart_1707782 baseEnd_1707782 := by
    simpa [prefixWord, tailWord_1707782, baseEnd_1707782] using wordTrace_append hprefix tailTrace_1707782
  have hstable : (prefixWord ++ tailWord_1707782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707782).length < 2 ^ (prefixWord ++ tailWord_1707782).sum := by decide
  have hdescent : baseEnd_1707782 < baseStart_1707782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707810 : List Nat := [3, 3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_1707810 : Nat := 118140960795 + 1707810 * 2 ^ 59
def prefixEnd_1707810 : Nat := 4983230072969 + 3 ^ 40 * 1707810 * 2
def baseEnd_1707810 : Nat := 97436377395007602135659

theorem tailTrace_1707810 : CollatzResearch.WordTrace tailWord_1707810 prefixEnd_1707810 97436377395007602135659 := by
  unfold tailWord_1707810
  simp only [CollatzResearch.WordTrace]
  refine ⟨15572236985725878893004221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41525965295269010381344589 15572236985725878893004221)
  ·
    refine ⟨5839588869647204584876583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15572236985725878893004221 5839588869647204584876583)
    ·
      refine ⟨8759383304470806877314875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839588869647204584876583 8759383304470806877314875)
      ·
        refine ⟨13139074956706210315972313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759383304470806877314875 13139074956706210315972313)
        ·
          refine ⟨9854306217529657736979235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13139074956706210315972313 9854306217529657736979235)
          ·
            refine ⟨14781459326294486605468853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9854306217529657736979235 14781459326294486605468853)
            ·
              refine ⟨1385761811840108119262705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14781459326294486605468853 1385761811840108119262705)
              ·
                refine ⟨1039321358880081089447029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385761811840108119262705 1039321358880081089447029)
                ·
                  refine ⟨97436377395007602135659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1039321358880081089447029 97436377395007602135659)
                  ·
                    rfl

theorem cell23_1707810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_1707810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707810 prefixEnd_1707810 := by exact prefixLift 1707810
  have htrace : WordTrace (prefixWord ++ tailWord_1707810) baseStart_1707810 baseEnd_1707810 := by
    simpa [prefixWord, tailWord_1707810, baseEnd_1707810] using wordTrace_append hprefix tailTrace_1707810
  have hstable : (prefixWord ++ tailWord_1707810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707810).length < 2 ^ (prefixWord ++ tailWord_1707810).sum := by decide
  have hdescent : baseEnd_1707810 < baseStart_1707810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707816 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1707816 : Nat := 118140960795 + 1707816 * 2 ^ 59
def prefixEnd_1707816 : Nat := 4983230072969 + 3 ^ 40 * 1707816 * 2
def baseEnd_1707816 : Nat := 876930477438995395745903

theorem tailTrace_1707816 : CollatzResearch.WordTrace tailWord_1707816 prefixEnd_1707816 876930477438995395745903 := by
  unfold tailWord_1707816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31144583390440889298367651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41526111187254519064490201 31144583390440889298367651)
  ·
    refine ⟨46716875085661333947551477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31144583390440889298367651 46716875085661333947551477)
    ·
      refine ⟨4379707039280750057582951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46716875085661333947551477 4379707039280750057582951)
      ·
        refine ⟨6569560558921125086374427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4379707039280750057582951 6569560558921125086374427)
        ·
          refine ⟨9854340838381687629561641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569560558921125086374427 9854340838381687629561641)
          ·
            refine ⟨7390755628786265722171231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9854340838381687629561641 7390755628786265722171231)
            ·
              refine ⟨11086133443179398583256847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390755628786265722171231 11086133443179398583256847)
              ·
                refine ⟨16629200164769097874885271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11086133443179398583256847 16629200164769097874885271)
                ·
                  refine ⟨24943800247153646812327907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16629200164769097874885271 24943800247153646812327907)
                  ·
                    refine ⟨37415700370730470218491861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24943800247153646812327907 37415700370730470218491861)
                    ·
                      refine ⟨876930477438995395745903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37415700370730470218491861 876930477438995395745903)
                      ·
                        rfl

theorem cell23_1707816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1707816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707816 prefixEnd_1707816 := by exact prefixLift 1707816
  have htrace : WordTrace (prefixWord ++ tailWord_1707816) baseStart_1707816 baseEnd_1707816 := by
    simpa [prefixWord, tailWord_1707816, baseEnd_1707816] using wordTrace_append hprefix tailTrace_1707816
  have hstable : (prefixWord ++ tailWord_1707816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707816).length < 2 ^ (prefixWord ++ tailWord_1707816).sum := by decide
  have hdescent : baseEnd_1707816 < baseStart_1707816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707843 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1707843 : Nat := 118140960795 + 1707843 * 2 ^ 59
def prefixEnd_1707843 : Nat := 4983230072969 + 3 ^ 40 * 1707843 * 2
def baseEnd_1707843 : Nat := 876944341416666790108279

theorem tailTrace_1707843 : CollatzResearch.WordTrace tailWord_1707843 prefixEnd_1707843 876944341416666790108279 := by
  unfold tailWord_1707843
  simp only [CollatzResearch.WordTrace]
  refine ⟨62290151551783962207968183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41526767701189308138645455 62290151551783962207968183)
  ·
    refine ⟨93435227327675943311952275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62290151551783962207968183 93435227327675943311952275)
    ·
      refine ⟨140152840991513914967928413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93435227327675943311952275 140152840991513914967928413)
      ·
        refine ⟨52557315371817718112973155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140152840991513914967928413 52557315371817718112973155)
        ·
          refine ⟨78835973057726577169459733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52557315371817718112973155 78835973057726577169459733)
          ·
            refine ⟨3695436237080933304818425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78835973057726577169459733 3695436237080933304818425)
            ·
              refine ⟨2771577177810699978613819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3695436237080933304818425 2771577177810699978613819)
              ·
                refine ⟨4157365766716049967920729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771577177810699978613819 4157365766716049967920729)
                ·
                  refine ⟨3118024325037037475940547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157365766716049967920729 3118024325037037475940547)
                  ·
                    refine ⟨4677036487555556213910821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3118024325037037475940547 4677036487555556213910821)
                    ·
                      refine ⟨876944341416666790108279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4677036487555556213910821 876944341416666790108279)
                      ·
                        rfl

theorem cell23_1707843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1707843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707843 prefixEnd_1707843 := by exact prefixLift 1707843
  have htrace : WordTrace (prefixWord ++ tailWord_1707843) baseStart_1707843 baseEnd_1707843 := by
    simpa [prefixWord, tailWord_1707843, baseEnd_1707843] using wordTrace_append hprefix tailTrace_1707843
  have hstable : (prefixWord ++ tailWord_1707843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707843).length < 2 ^ (prefixWord ++ tailWord_1707843).sum := by decide
  have hdescent : baseEnd_1707843 < baseStart_1707843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707894 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1707894 : Nat := 118140960795 + 1707894 * 2 ^ 59
def prefixEnd_1707894 : Nat := 4983230072969 + 3 ^ 40 * 1707894 * 2
def baseEnd_1707894 : Nat := 876970528930046090570545

theorem tailTrace_1707894 : CollatzResearch.WordTrace tailWord_1707894 prefixEnd_1707894 876970528930046090570545 := by
  unfold tailWord_1707894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893250729662449869879671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41528007783066131945383157 3893250729662449869879671)
  ·
    refine ⟨5839876094493674804819507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893250729662449869879671 5839876094493674804819507)
    ·
      refine ⟨8759814141740512207229261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839876094493674804819507 8759814141740512207229261)
      ·
        refine ⟨3284930303152692077710973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8759814141740512207229261 3284930303152692077710973)
        ·
          refine ⟨1231848863682259529141615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3284930303152692077710973 1231848863682259529141615)
          ·
            refine ⟨1847773295523389293712423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231848863682259529141615 1847773295523389293712423)
            ·
              refine ⟨2771659943285083940568635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847773295523389293712423 2771659943285083940568635)
              ·
                refine ⟨4157489914927625910852953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771659943285083940568635 4157489914927625910852953)
                ·
                  refine ⟨3118117436195719433139715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157489914927625910852953 3118117436195719433139715)
                  ·
                    refine ⟨4677176154293579149709573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3118117436195719433139715 4677176154293579149709573)
                    ·
                      refine ⟨876970528930046090570545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4677176154293579149709573 876970528930046090570545)
                      ·
                        rfl

theorem cell23_1707894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1707894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707894 prefixEnd_1707894 := by exact prefixLift 1707894
  have htrace : WordTrace (prefixWord ++ tailWord_1707894) baseStart_1707894 baseEnd_1707894 := by
    simpa [prefixWord, tailWord_1707894, baseEnd_1707894] using wordTrace_append hprefix tailTrace_1707894
  have hstable : (prefixWord ++ tailWord_1707894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707894).length < 2 ^ (prefixWord ++ tailWord_1707894).sum := by decide
  have hdescent : baseEnd_1707894 < baseStart_1707894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707913 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 1, 5]
def baseStart_1707913 : Nat := 118140960795 + 1707913 * 2 ^ 59
def prefixEnd_1707913 : Nat := 4983230072969 + 3 ^ 40 * 1707913 * 2
def baseEnd_1707913 : Nat := 292326761687493838744319

theorem tailTrace_1707913 : CollatzResearch.WordTrace tailWord_1707913 prefixEnd_1707913 292326761687493838744319 := by
  unfold tailWord_1707913
  simp only [CollatzResearch.WordTrace]
  refine ⟨62292704661530364163016393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41528469774353576108677595 62292704661530364163016393)
  ·
    refine ⟨46719528496147773122262295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62292704661530364163016393 46719528496147773122262295)
    ·
      refine ⟨70079292744221659683393443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46719528496147773122262295 70079292744221659683393443)
      ·
        refine ⟨105118939116332489525090165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70079292744221659683393443 105118939116332489525090165)
        ·
          refine ⟨9854900542156170892977203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105118939116332489525090165 9854900542156170892977203)
          ·
            refine ⟨14782350813234256339465805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9854900542156170892977203 14782350813234256339465805)
            ·
              refine ⟨5543381554962846127299677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14782350813234256339465805 5543381554962846127299677)
              ·
                refine ⟨2078768083111067297737379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5543381554962846127299677 2078768083111067297737379)
                ·
                  refine ⟨3118152124666600946606069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078768083111067297737379 3118152124666600946606069)
                  ·
                    refine ⟨292326761687493838744319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3118152124666600946606069 292326761687493838744319)
                    ·
                      rfl

theorem cell23_1707913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_1707913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707913 prefixEnd_1707913 := by exact prefixLift 1707913
  have htrace : WordTrace (prefixWord ++ tailWord_1707913) baseStart_1707913 baseEnd_1707913 := by
    simpa [prefixWord, tailWord_1707913, baseEnd_1707913] using wordTrace_append hprefix tailTrace_1707913
  have hstable : (prefixWord ++ tailWord_1707913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707913).length < 2 ^ (prefixWord ++ tailWord_1707913).sum := by decide
  have hdescent : baseEnd_1707913 < baseStart_1707913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707927 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 1, 1, 3]
def baseStart_1707927 : Nat := 118140960795 + 1707927 * 2 ^ 59
def prefixEnd_1707927 : Nat := 4983230072969 + 3 ^ 40 * 1707927 * 2
def baseEnd_1707927 : Nat := 876987473791644461457893

theorem tailTrace_1707927 : CollatzResearch.WordTrace tailWord_1707927 prefixEnd_1707927 876987473791644461457893 := by
  unfold tailWord_1707927
  simp only [CollatzResearch.WordTrace]
  refine ⟨62293215283479644554026035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41528810188986429702684023 62293215283479644554026035)
  ·
    refine ⟨93439822925219466831039053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62293215283479644554026035 93439822925219466831039053)
    ·
      refine ⟨35039933596957300061639645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93439822925219466831039053 35039933596957300061639645)
      ·
        refine ⟨13139975098858987523114867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35039933596957300061639645 13139975098858987523114867)
        ·
          refine ⟨19709962648288481284672301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139975098858987523114867 19709962648288481284672301)
          ·
            refine ⟨7391235993108180481752113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19709962648288481284672301 7391235993108180481752113)
            ·
              refine ⟨5543426994831135361314085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7391235993108180481752113 5543426994831135361314085)
              ·
                refine ⟨1039392561530837880246391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5543426994831135361314085 1039392561530837880246391)
                ·
                  refine ⟨1559088842296256820369587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039392561530837880246391 1559088842296256820369587)
                  ·
                    refine ⟨2338633263444385230554381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1559088842296256820369587 2338633263444385230554381)
                    ·
                      refine ⟨876987473791644461457893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2338633263444385230554381 876987473791644461457893)
                      ·
                        rfl

theorem cell23_1707927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_1707927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707927 prefixEnd_1707927 := by exact prefixLift 1707927
  have htrace : WordTrace (prefixWord ++ tailWord_1707927) baseStart_1707927 baseEnd_1707927 := by
    simpa [prefixWord, tailWord_1707927, baseEnd_1707927] using wordTrace_append hprefix tailTrace_1707927
  have hstable : (prefixWord ++ tailWord_1707927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707927).length < 2 ^ (prefixWord ++ tailWord_1707927).sum := by decide
  have hdescent : baseEnd_1707927 < baseStart_1707927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707934 : List Nat := [4, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1707934 : Nat := 118140960795 + 1707934 * 2 ^ 59
def prefixEnd_1707934 : Nat := 4983230072969 + 3 ^ 40 * 1707934 * 2
def baseEnd_1707934 : Nat := 97443452017358437118929

theorem tailTrace_1707934 : CollatzResearch.WordTrace tailWord_1707934 prefixEnd_1707934 97443452017358437118929 := by
  unfold tailWord_1707934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786683824306785593691357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41528980396302856499687237 7786683824306785593691357)
  ·
    refine ⟨2920006434115044597634259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7786683824306785593691357 2920006434115044597634259)
    ·
      refine ⟨4380009651172566896451389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920006434115044597634259 4380009651172566896451389)
      ·
        refine ⟨1642503619189712586169271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4380009651172566896451389 1642503619189712586169271)
        ·
          refine ⟨2463755428784568879253907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642503619189712586169271 2463755428784568879253907)
          ·
            refine ⟨3695633143176853318880861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463755428784568879253907 3695633143176853318880861)
            ·
              refine ⟨1385862428691319994580323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3695633143176853318880861 1385862428691319994580323)
              ·
                refine ⟨2078793643036979991870485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385862428691319994580323 2078793643036979991870485)
                ·
                  refine ⟨97443452017358437118929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2078793643036979991870485 97443452017358437118929)
                  ·
                    rfl

theorem cell23_1707934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1707934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707934 prefixEnd_1707934 := by exact prefixLift 1707934
  have htrace : WordTrace (prefixWord ++ tailWord_1707934) baseStart_1707934 baseEnd_1707934 := by
    simpa [prefixWord, tailWord_1707934, baseEnd_1707934] using wordTrace_append hprefix tailTrace_1707934
  have hstable : (prefixWord ++ tailWord_1707934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707934).length < 2 ^ (prefixWord ++ tailWord_1707934).sum := by decide
  have hdescent : baseEnd_1707934 < baseStart_1707934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1707994 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 2, 4]
def baseStart_1707994 : Nat := 118140960795 + 1707994 * 2 ^ 59
def prefixEnd_1707994 : Nat := 4983230072969 + 3 ^ 40 * 1707994 * 2
def baseEnd_1707994 : Nat := 292340625665165233106695

theorem tailTrace_1707994 : CollatzResearch.WordTrace tailWord_1707994 prefixEnd_1707994 292340625665165233106695 := by
  unfold tailWord_1707994
  simp only [CollatzResearch.WordTrace]
  refine ⟨15573914743559228749178759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41530439316157943331143357 15573914743559228749178759)
  ·
    refine ⟨23360872115338843123768139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15573914743559228749178759 23360872115338843123768139)
    ·
      refine ⟨35041308173008264685652209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23360872115338843123768139 35041308173008264685652209)
      ·
        refine ⟨26280981129756198514239157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35041308173008264685652209 26280981129756198514239157)
        ·
          refine ⟨2463841980914643610709921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26280981129756198514239157 2463841980914643610709921)
          ·
            refine ⟨1847881485685982708032441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2463841980914643610709921 1847881485685982708032441)
            ·
              refine ⟨1385911114264487031024331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847881485685982708032441 1385911114264487031024331)
              ·
                refine ⟨2078866671396730546536497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385911114264487031024331 2078866671396730546536497)
                ·
                  refine ⟨1559150003547547909902373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2078866671396730546536497 1559150003547547909902373)
                  ·
                    refine ⟨292340625665165233106695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559150003547547909902373 292340625665165233106695)
                    ·
                      rfl

theorem cell23_1707994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_1707994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1707994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1707994 prefixEnd_1707994 := by exact prefixLift 1707994
  have htrace : WordTrace (prefixWord ++ tailWord_1707994) baseStart_1707994 baseEnd_1707994 := by
    simpa [prefixWord, tailWord_1707994, baseEnd_1707994] using wordTrace_append hprefix tailTrace_1707994
  have hstable : (prefixWord ++ tailWord_1707994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1707994).length < 2 ^ (prefixWord ++ tailWord_1707994).sum := by decide
  have hdescent : baseEnd_1707994 < baseStart_1707994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1707994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708033 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1708033 : Nat := 118140960795 + 1708033 * 2 ^ 59
def prefixEnd_1708033 : Nat := 4983230072969 + 3 ^ 40 * 1708033 * 2
def baseEnd_1708033 : Nat := 292347300913673682244135

theorem tailTrace_1708033 : CollatzResearch.WordTrace tailWord_1708033 prefixEnd_1708033 292347300913673682244135 := by
  unfold tailWord_1708033
  simp only [CollatzResearch.WordTrace]
  refine ⟨62297081421095624657384753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41531387614063749771589835 62297081421095624657384753)
  ·
    refine ⟨46722811065821718493038565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62297081421095624657384753 46722811065821718493038565)
    ·
      refine ⟨8760527074841572217444731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46722811065821718493038565 8760527074841572217444731)
      ·
        refine ⟨13140790612262358326167097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8760527074841572217444731 13140790612262358326167097)
        ·
          refine ⟨9855592959196768744625323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13140790612262358326167097 9855592959196768744625323)
          ·
            refine ⟨14783389438795153116937985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855592959196768744625323 14783389438795153116937985)
            ·
              refine ⟨11087542079096364837703489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14783389438795153116937985 11087542079096364837703489)
              ·
                refine ⟨8315656559322273628277617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11087542079096364837703489 8315656559322273628277617)
                ·
                  refine ⟨6236742419491705221208213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8315656559322273628277617 6236742419491705221208213)
                  ·
                    refine ⟨292347300913673682244135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6236742419491705221208213 292347300913673682244135)
                    ·
                      rfl

theorem cell23_1708033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1708033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708033 prefixEnd_1708033 := by exact prefixLift 1708033
  have htrace : WordTrace (prefixWord ++ tailWord_1708033) baseStart_1708033 baseEnd_1708033 := by
    simpa [prefixWord, tailWord_1708033, baseEnd_1708033] using wordTrace_append hprefix tailTrace_1708033
  have hstable : (prefixWord ++ tailWord_1708033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708033).length < 2 ^ (prefixWord ++ tailWord_1708033).sum := by decide
  have hdescent : baseEnd_1708033 < baseStart_1708033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708040 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_1708040 : Nat := 118140960795 + 1708040 * 2 ^ 59
def prefixEnd_1708040 : Nat := 4983230072969 + 3 ^ 40 * 1708040 * 2
def baseEnd_1708040 : Nat := 877045497105602519344873

theorem tailTrace_1708040 : CollatzResearch.WordTrace tailWord_1708040 prefixEnd_1708040 877045497105602519344873 := by
  unfold tailWord_1708040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31148668366035132426444787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41531557821380176568593049 31148668366035132426444787)
  ·
    refine ⟨46723002549052698639667181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31148668366035132426444787 46723002549052698639667181)
    ·
      refine ⟨17521125955894761989875193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46723002549052698639667181 17521125955894761989875193)
      ·
        refine ⟨13140844466921071492406395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17521125955894761989875193 13140844466921071492406395)
        ·
          refine ⟨19711266700381607238609593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13140844466921071492406395 19711266700381607238609593)
          ·
            refine ⟨14783450025286205428957195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19711266700381607238609593 14783450025286205428957195)
            ·
              refine ⟨22175175037929308143435793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783450025286205428957195 22175175037929308143435793)
              ·
                refine ⟨16631381278446981107576845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22175175037929308143435793 16631381278446981107576845)
                ·
                  refine ⟨6236767979417617915341317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16631381278446981107576845 6236767979417617915341317)
                  ·
                    refine ⟨1169393996140803359126497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6236767979417617915341317 1169393996140803359126497)
                    ·
                      refine ⟨877045497105602519344873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169393996140803359126497 877045497105602519344873)
                      ·
                        rfl

theorem cell23_1708040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_1708040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708040 prefixEnd_1708040 := by exact prefixLift 1708040
  have htrace : WordTrace (prefixWord ++ tailWord_1708040) baseStart_1708040 baseEnd_1708040 := by
    simpa [prefixWord, tailWord_1708040, baseEnd_1708040] using wordTrace_append hprefix tailTrace_1708040
  have hstable : (prefixWord ++ tailWord_1708040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708040).length < 2 ^ (prefixWord ++ tailWord_1708040).sum := by decide
  have hdescent : baseEnd_1708040 < baseStart_1708040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708043 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 3]
def baseStart_1708043 : Nat := 118140960795 + 1708043 * 2 ^ 59
def prefixEnd_1708043 : Nat := 4983230072969 + 3 ^ 40 * 1708043 * 2
def baseEnd_1708043 : Nat := 877047037547566007607359

theorem tailTrace_1708043 : CollatzResearch.WordTrace tailWord_1708043 prefixEnd_1708043 877047037547566007607359 := by
  unfold tailWord_1708043
  simp only [CollatzResearch.WordTrace]
  refine ⟨62297446151059396365248783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41531630767372930910165855 62297446151059396365248783)
  ·
    refine ⟨93446169226589094547873175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62297446151059396365248783 93446169226589094547873175)
    ·
      refine ⟨140169253839883641821809763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93446169226589094547873175 140169253839883641821809763)
      ·
        refine ⟨210253880759825462732714645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140169253839883641821809763 210253880759825462732714645)
        ·
          refine ⟨9855650660616818565595999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 210253880759825462732714645 9855650660616818565595999)
          ·
            refine ⟨14783475990925227848393999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855650660616818565595999 14783475990925227848393999)
            ·
              refine ⟨22175213986387841772590999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783475990925227848393999 22175213986387841772590999)
              ·
                refine ⟨33262820979581762658886499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22175213986387841772590999 33262820979581762658886499)
                ·
                  refine ⟨49894231469372643988329749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33262820979581762658886499 49894231469372643988329749)
                  ·
                    refine ⟨2338792100126842686952957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49894231469372643988329749 2338792100126842686952957)
                    ·
                      refine ⟨877047037547566007607359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2338792100126842686952957 877047037547566007607359)
                      ·
                        rfl

theorem cell23_1708043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 3].length) (baseStart_1708043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708043 prefixEnd_1708043 := by exact prefixLift 1708043
  have htrace : WordTrace (prefixWord ++ tailWord_1708043) baseStart_1708043 baseEnd_1708043 := by
    simpa [prefixWord, tailWord_1708043, baseEnd_1708043] using wordTrace_append hprefix tailTrace_1708043
  have hstable : (prefixWord ++ tailWord_1708043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708043).length < 2 ^ (prefixWord ++ tailWord_1708043).sum := by decide
  have hdescent : baseEnd_1708043 < baseStart_1708043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708063 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 7]
def baseStart_1708063 : Nat := 118140960795 + 1708063 * 2 ^ 59
def prefixEnd_1708063 : Nat := 4983230072969 + 3 ^ 40 * 1708063 * 2
def baseEnd_1708063 : Nat := 97450811906739547706363

theorem tailTrace_1708063 : CollatzResearch.WordTrace tailWord_1708063 prefixEnd_1708063 97450811906739547706363 := by
  unfold tailWord_1708063
  simp only [CollatzResearch.WordTrace]
  refine ⟨62298175610986939780976843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41532117073991293187317895 62298175610986939780976843)
  ·
    refine ⟨93447263416480409671465265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62298175610986939780976843 93447263416480409671465265)
    ·
      refine ⟨70085447562360307253598949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93447263416480409671465265 70085447562360307253598949)
      ·
        refine ⟨13141021417942557610049803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70085447562360307253598949 13141021417942557610049803)
        ·
          refine ⟨19711532126913836415074705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141021417942557610049803 19711532126913836415074705)
          ·
            refine ⟨14783649095185377311306029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19711532126913836415074705 14783649095185377311306029)
            ·
              refine ⟨5543868410694516491739761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14783649095185377311306029 5543868410694516491739761)
              ·
                refine ⟨4157901308020887368804821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5543868410694516491739761 4157901308020887368804821)
                ·
                  refine ⟨97450811906739547706363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4157901308020887368804821 97450811906739547706363)
                  ·
                    rfl

theorem cell23_1708063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 7].length) (baseStart_1708063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708063 prefixEnd_1708063 := by exact prefixLift 1708063
  have htrace : WordTrace (prefixWord ++ tailWord_1708063) baseStart_1708063 baseEnd_1708063 := by
    simpa [prefixWord, tailWord_1708063, baseEnd_1708063] using wordTrace_append hprefix tailTrace_1708063
  have hstable : (prefixWord ++ tailWord_1708063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708063).length < 2 ^ (prefixWord ++ tailWord_1708063).sum := by decide
  have hdescent : baseEnd_1708063 < baseStart_1708063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708080 : List Nat := [2, 1, 1, 1, 2, 5, 1, 5, 5]
def baseStart_1708080 : Nat := 118140960795 + 1708080 * 2 ^ 59
def prefixEnd_1708080 : Nat := 4983230072969 + 3 ^ 40 * 1708080 * 2
def baseEnd_1708080 : Nat := 97451781814642484760521

theorem tailTrace_1708080 : CollatzResearch.WordTrace tailWord_1708080 prefixEnd_1708080 97451781814642484760521 := by
  unfold tailWord_1708080
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149397825962675842172847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41532530434616901122897129 31149397825962675842172847)
  ·
    refine ⟨46724096738944013763259271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31149397825962675842172847 46724096738944013763259271)
    ·
      refine ⟨70086145108416020644888907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46724096738944013763259271 70086145108416020644888907)
      ·
        refine ⟨105129217662624030967333361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70086145108416020644888907 105129217662624030967333361)
        ·
          refine ⟨78846913246968023225500021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105129217662624030967333361 78846913246968023225500021)
          ·
            refine ⟨7391898116903252177390627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78846913246968023225500021 7391898116903252177390627)
            ·
              refine ⟨11087847175354878266085941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391898116903252177390627 11087847175354878266085941)
              ·
                refine ⟨1039485672689519837445557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11087847175354878266085941 1039485672689519837445557)
                ·
                  refine ⟨97451781814642484760521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1039485672689519837445557 97451781814642484760521)
                  ·
                    rfl

theorem cell23_1708080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 5, 5].length) (baseStart_1708080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708080 prefixEnd_1708080 := by exact prefixLift 1708080
  have htrace : WordTrace (prefixWord ++ tailWord_1708080) baseStart_1708080 baseEnd_1708080 := by
    simpa [prefixWord, tailWord_1708080, baseEnd_1708080] using wordTrace_append hprefix tailTrace_1708080
  have hstable : (prefixWord ++ tailWord_1708080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708080).length < 2 ^ (prefixWord ++ tailWord_1708080).sum := by decide
  have hdescent : baseEnd_1708080 < baseStart_1708080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708097 : List Nat := [1, 2, 5, 1, 2, 1, 2, 4, 5]
def baseStart_1708097 : Nat := 118140960795 + 1708097 * 2 ^ 59
def prefixEnd_1708097 : Nat := 4983230072969 + 3 ^ 40 * 1708097 * 2
def baseEnd_1708097 : Nat := 97452751722545421814679

theorem tailTrace_1708097 : CollatzResearch.WordTrace tailWord_1708097 prefixEnd_1708097 97452751722545421814679 := by
  unfold tailWord_1708097
  simp only [CollatzResearch.WordTrace]
  refine ⟨62299415692863763587714545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41532943795242509058476363 62299415692863763587714545)
  ·
    refine ⟨46724561769647822690785909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62299415692863763587714545 46724561769647822690785909)
    ·
      refine ⟨4380427665904483377261179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46724561769647822690785909 4380427665904483377261179)
      ·
        refine ⟨6570641498856725065891769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380427665904483377261179 6570641498856725065891769)
        ·
          refine ⟨4927981124142543799418827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6570641498856725065891769 4927981124142543799418827)
          ·
            refine ⟨7391971686213815699128241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927981124142543799418827 7391971686213815699128241)
            ·
              refine ⟨5543978764660361774346181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7391971686213815699128241 5543978764660361774346181)
              ·
                refine ⟨1039496018373817832689909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5543978764660361774346181 1039496018373817832689909)
                ·
                  refine ⟨97452751722545421814679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1039496018373817832689909 97452751722545421814679)
                  ·
                    rfl

theorem cell23_1708097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 5].length) (baseStart_1708097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708097 prefixEnd_1708097 := by exact prefixLift 1708097
  have htrace : WordTrace (prefixWord ++ tailWord_1708097) baseStart_1708097 baseEnd_1708097 := by
    simpa [prefixWord, tailWord_1708097, baseEnd_1708097] using wordTrace_append hprefix tailTrace_1708097
  have hstable : (prefixWord ++ tailWord_1708097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708097).length < 2 ^ (prefixWord ++ tailWord_1708097).sum := by decide
  have hdescent : baseEnd_1708097 < baseStart_1708097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708103 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1708103 : Nat := 118140960795 + 1708103 * 2 ^ 59
def prefixEnd_1708103 : Nat := 4983230072969 + 3 ^ 40 * 1708103 * 2
def baseEnd_1708103 : Nat := 877077846386835772857083

theorem tailTrace_1708103 : CollatzResearch.WordTrace tailWord_1708103 prefixEnd_1708103 877077846386835772857083 := by
  unfold tailWord_1708103
  simp only [CollatzResearch.WordTrace]
  refine ⟨62299634530842026612432963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41533089687228017741621975 62299634530842026612432963)
  ·
    refine ⟨93449451796263039918649445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62299634530842026612432963 93449451796263039918649445)
    ·
      refine ⟨17521772211799319984746771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93449451796263039918649445 17521772211799319984746771)
      ·
        refine ⟨26282658317698979977120157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17521772211799319984746771 26282658317698979977120157)
        ·
          refine ⟨9855996869137117491420059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26282658317698979977120157 9855996869137117491420059)
          ·
            refine ⟨14783995303705676237130089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855996869137117491420059 14783995303705676237130089)
            ·
              refine ⟨11087996477779257177847567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14783995303705676237130089 11087996477779257177847567)
              ·
                refine ⟨16631994716668885766771351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11087996477779257177847567 16631994716668885766771351)
                ·
                  refine ⟨24947992075003328650157027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16631994716668885766771351 24947992075003328650157027)
                  ·
                    refine ⟨37421988112504992975235541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24947992075003328650157027 37421988112504992975235541)
                    ·
                      refine ⟨877077846386835772857083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37421988112504992975235541 877077846386835772857083)
                      ·
                        rfl

theorem cell23_1708103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1708103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708103 prefixEnd_1708103 := by exact prefixLift 1708103
  have htrace : WordTrace (prefixWord ++ tailWord_1708103) baseStart_1708103 baseEnd_1708103 := by
    simpa [prefixWord, tailWord_1708103, baseEnd_1708103] using wordTrace_append hprefix tailTrace_1708103
  have hstable : (prefixWord ++ tailWord_1708103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708103).length < 2 ^ (prefixWord ++ tailWord_1708103).sum := by decide
  have hdescent : baseEnd_1708103 < baseStart_1708103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708157 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1708157 : Nat := 118140960795 + 1708157 * 2 ^ 59
def prefixEnd_1708157 : Nat := 4983230072969 + 3 ^ 40 * 1708157 * 2
def baseEnd_1708157 : Nat := 292368524780726187193945

theorem tailTrace_1708157 : CollatzResearch.WordTrace tailWord_1708157 prefixEnd_1708157 292368524780726187193945 := by
  unfold tailWord_1708157
  simp only [CollatzResearch.WordTrace]
  refine ⟨62301604072646393834898725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41534402715097595889932483 62301604072646393834898725)
  ·
    refine ⟨11681550763621198844043511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62301604072646393834898725 11681550763621198844043511)
    ·
      refine ⟨17522326145431798266065267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11681550763621198844043511 17522326145431798266065267)
      ·
        refine ⟨26283489218147697399097901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17522326145431798266065267 26283489218147697399097901)
        ·
          refine ⟨9856308456805386524661713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26283489218147697399097901 9856308456805386524661713)
          ·
            refine ⟨7392231342604039893496285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9856308456805386524661713 7392231342604039893496285)
            ·
              refine ⟨2772086753476514960061107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7392231342604039893496285 2772086753476514960061107)
              ·
                refine ⟨4158130130214772440091661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772086753476514960061107 4158130130214772440091661)
                ·
                  refine ⟨1559298798830539665034373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4158130130214772440091661 1559298798830539665034373)
                  ·
                    refine ⟨292368524780726187193945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559298798830539665034373 292368524780726187193945)
                    ·
                      rfl

theorem cell23_1708157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1708157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708157 prefixEnd_1708157 := by exact prefixLift 1708157
  have htrace : WordTrace (prefixWord ++ tailWord_1708157) baseStart_1708157 baseEnd_1708157 := by
    simpa [prefixWord, tailWord_1708157, baseEnd_1708157] using wordTrace_append hprefix tailTrace_1708157
  have hstable : (prefixWord ++ tailWord_1708157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708157).length < 2 ^ (prefixWord ++ tailWord_1708157).sum := by decide
  have hdescent : baseEnd_1708157 < baseStart_1708157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708184 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1708184 : Nat := 118140960795 + 1708184 * 2 ^ 59
def prefixEnd_1708184 : Nat := 4983230072969 + 3 ^ 40 * 1708184 * 2
def baseEnd_1708184 : Nat := 877119438319849955944211

theorem tailTrace_1708184 : CollatzResearch.WordTrace tailWord_1708184 prefixEnd_1708184 877119438319849955944211 := by
  unfold tailWord_1708184
  simp only [CollatzResearch.WordTrace]
  refine ⟨31151294421774288723065803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41535059229032384964087737 31151294421774288723065803)
  ·
    refine ⟨46726941632661433084598705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31151294421774288723065803 46726941632661433084598705)
    ·
      refine ⟨35045206224496074813449029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46726941632661433084598705 35045206224496074813449029)
      ·
        refine ⟨6570976167093014027521693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35045206224496074813449029 6570976167093014027521693)
        ·
          refine ⟨2464116062659880260320635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6570976167093014027521693 2464116062659880260320635)
          ·
            refine ⟨3696174093989820390480953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464116062659880260320635 3696174093989820390480953)
            ·
              refine ⟨2772130570492365292860715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696174093989820390480953 2772130570492365292860715)
              ·
                refine ⟨4158195855738547939291073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772130570492365292860715 4158195855738547939291073)
                ·
                  refine ⟨3118646891803910954468305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4158195855738547939291073 3118646891803910954468305)
                  ·
                    refine ⟨2338985168852933215851229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3118646891803910954468305 2338985168852933215851229)
                    ·
                      refine ⟨877119438319849955944211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2338985168852933215851229 877119438319849955944211)
                      ·
                        rfl

theorem cell23_1708184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1708184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708184 prefixEnd_1708184 := by exact prefixLift 1708184
  have htrace : WordTrace (prefixWord ++ tailWord_1708184) baseStart_1708184 baseEnd_1708184 := by
    simpa [prefixWord, tailWord_1708184, baseEnd_1708184] using wordTrace_append hprefix tailTrace_1708184
  have hstable : (prefixWord ++ tailWord_1708184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708184).length < 2 ^ (prefixWord ++ tailWord_1708184).sum := by decide
  have hdescent : baseEnd_1708184 < baseStart_1708184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708264 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1708264 : Nat := 118140960795 + 1708264 * 2 ^ 59
def prefixEnd_1708264 : Nat := 4983230072969 + 3 ^ 40 * 1708264 * 2
def baseEnd_1708264 : Nat := 292386838924069880981281

theorem tailTrace_1708264 : CollatzResearch.WordTrace tailWord_1708264 prefixEnd_1708264 292386838924069880981281 := by
  unfold tailWord_1708264
  simp only [CollatzResearch.WordTrace]
  refine ⟨31152753341629375554521923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41537004455505834072695897 31152753341629375554521923)
  ·
    refine ⟨46729130012444063331782885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31152753341629375554521923 46729130012444063331782885)
    ·
      refine ⟨8761711877333261874709291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46729130012444063331782885 8761711877333261874709291)
      ·
        refine ⟨13142567815999892812063937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761711877333261874709291 13142567815999892812063937)
        ·
          refine ⟨9856925861999919609047953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13142567815999892812063937 9856925861999919609047953)
          ·
            refine ⟨7392694396499939706785965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9856925861999919609047953 7392694396499939706785965)
            ·
              refine ⟨2772260398687477390044737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7392694396499939706785965 2772260398687477390044737)
              ·
                refine ⟨2079195299015608042533553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772260398687477390044737 2079195299015608042533553)
                ·
                  refine ⟨1559396474261706031900165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079195299015608042533553 1559396474261706031900165)
                  ·
                    refine ⟨292386838924069880981281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559396474261706031900165 292386838924069880981281)
                    ·
                      rfl

theorem cell23_1708264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1708264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708264 prefixEnd_1708264 := by exact prefixLift 1708264
  have htrace : WordTrace (prefixWord ++ tailWord_1708264) baseStart_1708264 baseEnd_1708264 := by
    simpa [prefixWord, tailWord_1708264, baseEnd_1708264] using wordTrace_append hprefix tailTrace_1708264
  have hstable : (prefixWord ++ tailWord_1708264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708264).length < 2 ^ (prefixWord ++ tailWord_1708264).sum := by decide
  have hdescent : baseEnd_1708264 < baseStart_1708264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708270 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_1708270 : Nat := 118140960795 + 1708270 * 2 ^ 59
def prefixEnd_1708270 : Nat := 4983230072969 + 3 ^ 40 * 1708270 * 2
def baseEnd_1708270 : Nat := 877163597656136619468815

theorem tailTrace_1708270 : CollatzResearch.WordTrace tailWord_1708270 prefixEnd_1708270 877163597656136619468815 := by
  unfold tailWord_1708270
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788215690154626766720283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41537150347491342755841509 7788215690154626766720283)
  ·
    refine ⟨11682323535231940150080425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7788215690154626766720283 11682323535231940150080425)
    ·
      refine ⟨8761742651423955112560319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11682323535231940150080425 8761742651423955112560319)
      ·
        refine ⟨13142613977135932668840479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761742651423955112560319 13142613977135932668840479)
        ·
          refine ⟨19713920965703899003260719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13142613977135932668840479 19713920965703899003260719)
          ·
            refine ⟨29570881448555848504891079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19713920965703899003260719 29570881448555848504891079)
            ·
              refine ⟨44356322172833772757336619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29570881448555848504891079 44356322172833772757336619)
              ·
                refine ⟨66534483259250659136004929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44356322172833772757336619 66534483259250659136004929)
                ·
                  refine ⟨49900862444437994352003697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66534483259250659136004929 49900862444437994352003697)
                  ·
                    refine ⟨37425646833328495764002773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49900862444437994352003697 37425646833328495764002773)
                    ·
                      refine ⟨877163597656136619468815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37425646833328495764002773 877163597656136619468815)
                      ·
                        rfl

theorem cell23_1708270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_1708270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708270 prefixEnd_1708270 := by exact prefixLift 1708270
  have htrace : WordTrace (prefixWord ++ tailWord_1708270) baseStart_1708270 baseEnd_1708270 := by
    simpa [prefixWord, tailWord_1708270, baseEnd_1708270] using wordTrace_append hprefix tailTrace_1708270
  have hstable : (prefixWord ++ tailWord_1708270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708270).length < 2 ^ (prefixWord ++ tailWord_1708270).sum := by decide
  have hdescent : baseEnd_1708270 < baseStart_1708270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708271 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 3, 2, 2]
def baseStart_1708271 : Nat := 118140960795 + 1708271 * 2 ^ 59
def prefixEnd_1708271 : Nat := 4983230072969 + 3 ^ 40 * 1708271 * 2
def baseEnd_1708271 : Nat := 877164111136791115556311

theorem tailTrace_1708271 : CollatzResearch.WordTrace tailWord_1708271 prefixEnd_1708271 877164111136791115556311 := by
  unfold tailWord_1708271
  simp only [CollatzResearch.WordTrace]
  refine ⟨62305761994233391304548667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41537174662822260869699111 62305761994233391304548667)
  ·
    refine ⟨93458642991350086956823001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62305761994233391304548667 93458642991350086956823001)
    ·
      refine ⟨70093982243512565217617251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93458642991350086956823001 70093982243512565217617251)
      ·
        refine ⟨105140973365268847826425877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70093982243512565217617251 105140973365268847826425877)
        ·
          refine ⟨4928483126496977241863713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105140973365268847826425877 4928483126496977241863713)
          ·
            refine ⟨3696362344872732931397785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4928483126496977241863713 3696362344872732931397785)
            ·
              refine ⟨2772271758654549698548339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696362344872732931397785 2772271758654549698548339)
              ·
                refine ⟨4158407637981824547822509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772271758654549698548339 4158407637981824547822509)
                ·
                  refine ⟨1559402864243184205433441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4158407637981824547822509 1559402864243184205433441)
                  ·
                    refine ⟨1169552148182388154075081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1559402864243184205433441 1169552148182388154075081)
                    ·
                      refine ⟨877164111136791115556311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169552148182388154075081 877164111136791115556311)
                      ·
                        rfl

theorem cell23_1708271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 2, 2].length) (baseStart_1708271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708271 prefixEnd_1708271 := by exact prefixLift 1708271
  have htrace : WordTrace (prefixWord ++ tailWord_1708271) baseStart_1708271 baseEnd_1708271 := by
    simpa [prefixWord, tailWord_1708271, baseEnd_1708271] using wordTrace_append hprefix tailTrace_1708271
  have hstable : (prefixWord ++ tailWord_1708271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708271).length < 2 ^ (prefixWord ++ tailWord_1708271).sum := by decide
  have hdescent : baseEnd_1708271 < baseStart_1708271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708284 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_1708284 : Nat := 118140960795 + 1708284 * 2 ^ 59
def prefixEnd_1708284 : Nat := 4983230072969 + 3 ^ 40 * 1708284 * 2
def baseEnd_1708284 : Nat := 877170786385299564693751

theorem tailTrace_1708284 : CollatzResearch.WordTrace tailWord_1708284 prefixEnd_1708284 877170786385299564693751 := by
  unfold tailWord_1708284
  simp only [CollatzResearch.WordTrace]
  refine ⟨31153118071593147262385953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41537490762124196349847937 31153118071593147262385953)
  ·
    refine ⟨23364838553694860446789465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31153118071593147262385953 23364838553694860446789465)
    ·
      refine ⟨17523628915271145335092099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23364838553694860446789465 17523628915271145335092099)
      ·
        refine ⟨26285443372906718002638149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17523628915271145335092099 26285443372906718002638149)
        ·
          refine ⟨4928520632420009625494653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26285443372906718002638149 4928520632420009625494653)
          ·
            refine ⟨1848195237157503609560495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4928520632420009625494653 1848195237157503609560495)
            ·
              refine ⟨2772292855736255414340743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848195237157503609560495 2772292855736255414340743)
              ·
                refine ⟨4158439283604383121511115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772292855736255414340743 4158439283604383121511115)
                ·
                  refine ⟨6237658925406574682266673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158439283604383121511115 6237658925406574682266673)
                  ·
                    refine ⟨4678244194054931011700005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6237658925406574682266673 4678244194054931011700005)
                    ·
                      refine ⟨877170786385299564693751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4678244194054931011700005 877170786385299564693751)
                      ·
                        rfl

theorem cell23_1708284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_1708284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708284 prefixEnd_1708284 := by exact prefixLift 1708284
  have htrace : WordTrace (prefixWord ++ tailWord_1708284) baseStart_1708284 baseEnd_1708284 := by
    simpa [prefixWord, tailWord_1708284, baseEnd_1708284] using wordTrace_append hprefix tailTrace_1708284
  have hstable : (prefixWord ++ tailWord_1708284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708284).length < 2 ^ (prefixWord ++ tailWord_1708284).sum := by decide
  have hdescent : baseEnd_1708284 < baseStart_1708284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708300 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1708300 : Nat := 118140960795 + 1708300 * 2 ^ 59
def prefixEnd_1708300 : Nat := 4983230072969 + 3 ^ 40 * 1708300 * 2
def baseEnd_1708300 : Nat := 877179002075771502093677

theorem tailTrace_1708300 : CollatzResearch.WordTrace tailWord_1708300 prefixEnd_1708300 877179002075771502093677 := by
  unfold tailWord_1708300
  simp only [CollatzResearch.WordTrace]
  refine ⟨31153409855564164628677177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41537879807418886171569569 31153409855564164628677177)
  ·
    refine ⟨23365057391673123471507883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31153409855564164628677177 23365057391673123471507883)
    ·
      refine ⟨35047586087509685207261825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23365057391673123471507883 35047586087509685207261825)
      ·
        refine ⟨26285689565632263905446369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35047586087509685207261825 26285689565632263905446369)
        ·
          refine ⟨19714267174224197929084777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26285689565632263905446369 19714267174224197929084777)
          ·
            refine ⟨14785700380668148446813583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19714267174224197929084777 14785700380668148446813583)
            ·
              refine ⟨22178550571002222670220375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14785700380668148446813583 22178550571002222670220375)
              ·
                refine ⟨33267825856503334005330563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22178550571002222670220375 33267825856503334005330563)
                ·
                  refine ⟨49901738784755001007995845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33267825856503334005330563 49901738784755001007995845)
                  ·
                    refine ⟨9356576022141562688999221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49901738784755001007995845 9356576022141562688999221)
                    ·
                      refine ⟨877179002075771502093677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9356576022141562688999221 877179002075771502093677)
                      ·
                        rfl

theorem cell23_1708300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1708300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708300 prefixEnd_1708300 := by exact prefixLift 1708300
  have htrace : WordTrace (prefixWord ++ tailWord_1708300) baseStart_1708300 baseEnd_1708300 := by
    simpa [prefixWord, tailWord_1708300, baseEnd_1708300] using wordTrace_append hprefix tailTrace_1708300
  have hstable : (prefixWord ++ tailWord_1708300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708300).length < 2 ^ (prefixWord ++ tailWord_1708300).sum := by decide
  have hdescent : baseEnd_1708300 < baseStart_1708300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708377 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_1708377 : Nat := 118140960795 + 1708377 * 2 ^ 59
def prefixEnd_1708377 : Nat := 4983230072969 + 3 ^ 40 * 1708377 * 2
def baseEnd_1708377 : Nat := 877218540086167700830823

theorem tailTrace_1708377 : CollatzResearch.WordTrace tailWord_1708377 prefixEnd_1708377 877218540086167700830823 := by
  unfold tailWord_1708377
  simp only [CollatzResearch.WordTrace]
  refine ⟨62309628131849371407907385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41539752087899580938604923 62309628131849371407907385)
  ·
    refine ⟨46732221098887028555930539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62309628131849371407907385 46732221098887028555930539)
    ·
      refine ⟨70098331648330542833895809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46732221098887028555930539 70098331648330542833895809)
      ·
        refine ⟨52573748736247907125421857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70098331648330542833895809 52573748736247907125421857)
        ·
          refine ⟨39430311552185930344066393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52573748736247907125421857 39430311552185930344066393)
          ·
            refine ⟨29572733664139447758049795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39430311552185930344066393 29572733664139447758049795)
            ·
              refine ⟨44359100496209171637074693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29572733664139447758049795 44359100496209171637074693)
              ·
                refine ⟨8317331343039219681951505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44359100496209171637074693 8317331343039219681951505)
                ·
                  refine ⟨6237998507279414761463629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8317331343039219681951505 6237998507279414761463629)
                  ·
                    refine ⟨2339249440229780535548861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6237998507279414761463629 2339249440229780535548861)
                    ·
                      refine ⟨877218540086167700830823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2339249440229780535548861 877218540086167700830823)
                      ·
                        rfl

theorem cell23_1708377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_1708377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708377 prefixEnd_1708377 := by exact prefixLift 1708377
  have htrace : WordTrace (prefixWord ++ tailWord_1708377) baseStart_1708377 baseEnd_1708377 := by
    simpa [prefixWord, tailWord_1708377, baseEnd_1708377] using wordTrace_append hprefix tailTrace_1708377
  have hstable : (prefixWord ++ tailWord_1708377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708377).length < 2 ^ (prefixWord ++ tailWord_1708377).sum := by decide
  have hdescent : baseEnd_1708377 < baseStart_1708377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
