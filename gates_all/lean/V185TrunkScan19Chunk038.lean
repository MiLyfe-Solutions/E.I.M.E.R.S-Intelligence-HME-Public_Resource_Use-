import V185TrunkScan19Chunk037

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_381975 : List Nat := [1, 1, 3, 5, 1, 2, 1, 5]
def baseStart_381975 : Nat := 118140960795 + 381975 * 2 ^ 59
def prefixEnd_381975 : Nat := 4983230072969 + 3 ^ 40 * 381975 * 2
def baseEnd_381975 : Nat := 116229198815554521336791

theorem tailTrace_381975 : CollatzResearch.WordTrace tailWord_381975 prefixEnd_381975 116229198815554521336791 := by
  unfold tailWord_381975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13931772791177285981395379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9287848527451523987596919 13931772791177285981395379)
  ·
    refine ⟨20897659186765928972093069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13931772791177285981395379 20897659186765928972093069)
    ·
      refine ⟨7836622195037223364534901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20897659186765928972093069 7836622195037223364534901)
      ·
        refine ⟨734683330784739690425147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7836622195037223364534901 734683330784739690425147)
        ·
          refine ⟨1102024996177109535637721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734683330784739690425147 1102024996177109535637721)
          ·
            refine ⟨826518747132832151728291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102024996177109535637721 826518747132832151728291)
            ·
              refine ⟨1239778120699248227592437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826518747132832151728291 1239778120699248227592437)
              ·
                refine ⟨116229198815554521336791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1239778120699248227592437 116229198815554521336791)
                ·
                  rfl

theorem cell19_381975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_381975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_381975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_381975 prefixEnd_381975 := by exact prefixLift 381975
  have htrace : WordTrace (prefixWord ++ tailWord_381975) baseStart_381975 baseEnd_381975 := by
    simpa [prefixWord, tailWord_381975, baseEnd_381975] using wordTrace_append hprefix tailTrace_381975
  have hstable : (prefixWord ++ tailWord_381975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381975).length < 2 ^ (prefixWord ++ tailWord_381975).sum := by decide
  have hdescent : baseEnd_381975 < baseStart_381975 := by decide
  rcases family_descends (prefixWord ++ tailWord_381975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382013 : List Nat := [1, 4, 1, 3, 1, 3, 2, 4]
def baseStart_382013 : Nat := 118140960795 + 382013 * 2 ^ 59
def prefixEnd_382013 : Nat := 4983230072969 + 3 ^ 40 * 382013 * 2
def baseEnd_382013 : Nat := 116240761639181692492243

theorem tailTrace_382013 : CollatzResearch.WordTrace tailWord_382013 prefixEnd_382013 116240761639181692492243 := by
  unfold tailWord_382013
  simp only [CollatzResearch.WordTrace]
  refine ⟨13933158765039618471278693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9288772510026412314185795 13933158765039618471278693)
  ·
    refine ⟨2612467268444928463364755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13933158765039618471278693 2612467268444928463364755)
    ·
      refine ⟨3918700902667392695047133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2612467268444928463364755 3918700902667392695047133)
      ·
        refine ⟨1469512838500272260642675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3918700902667392695047133 1469512838500272260642675)
        ·
          refine ⟨2204269257750408390964013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469512838500272260642675 2204269257750408390964013)
          ·
            refine ⟨826600971656403146611505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2204269257750408390964013 826600971656403146611505)
            ·
              refine ⟨619950728742302359958629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826600971656403146611505 619950728742302359958629)
              ·
                refine ⟨116240761639181692492243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 619950728742302359958629 116240761639181692492243)
                ·
                  rfl

theorem cell19_382013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_382013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382013 prefixEnd_382013 := by exact prefixLift 382013
  have htrace : WordTrace (prefixWord ++ tailWord_382013) baseStart_382013 baseEnd_382013 := by
    simpa [prefixWord, tailWord_382013, baseEnd_382013] using wordTrace_append hprefix tailTrace_382013
  have hstable : (prefixWord ++ tailWord_382013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382013).length < 2 ^ (prefixWord ++ tailWord_382013).sum := by decide
  have hdescent : baseEnd_382013 < baseStart_382013 := by decide
  rcases family_descends (prefixWord ++ tailWord_382013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382072 : List Nat := [2, 1, 2, 1, 1, 1, 7, 4]
def baseStart_382072 : Nat := 118140960795 + 382072 * 2 ^ 59
def prefixEnd_382072 : Nat := 4983230072969 + 3 ^ 40 * 382072 * 2
def baseEnd_382072 : Nat := 116258714444287037180971

theorem tailTrace_382072 : CollatzResearch.WordTrace tailWord_382072 prefixEnd_382072 116258714444287037180971 := by
  unfold tailWord_382072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967655335912935773838235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9290207114550581031784313 6967655335912935773838235)
  ·
    refine ⟨10451483003869403660757353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6967655335912935773838235 10451483003869403660757353)
    ·
      refine ⟨7838612252902052745568015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10451483003869403660757353 7838612252902052745568015)
      ·
        refine ⟨11757918379353079118352023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7838612252902052745568015 11757918379353079118352023)
        ·
          refine ⟨17636877569029618677528035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757918379353079118352023 17636877569029618677528035)
          ·
            refine ⟨26455316353544428016292053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17636877569029618677528035 26455316353544428016292053)
            ·
              refine ⟨620046477036197531631845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 26455316353544428016292053 620046477036197531631845)
              ·
                refine ⟨116258714444287037180971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620046477036197531631845 116258714444287037180971)
                ·
                  rfl

theorem cell19_382072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_382072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382072 prefixEnd_382072 := by exact prefixLift 382072
  have htrace : WordTrace (prefixWord ++ tailWord_382072) baseStart_382072 baseEnd_382072 := by
    simpa [prefixWord, tailWord_382072, baseEnd_382072] using wordTrace_append hprefix tailTrace_382072
  have hstable : (prefixWord ++ tailWord_382072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382072).length < 2 ^ (prefixWord ++ tailWord_382072).sum := by decide
  have hdescent : baseEnd_382072 < baseStart_382072 := by decide
  rcases family_descends (prefixWord ++ tailWord_382072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382089 : List Nat := [1, 2, 1, 1, 4, 4, 3, 3]
def baseStart_382089 : Nat := 118140960795 + 382089 * 2 ^ 59
def prefixEnd_382089 : Nat := 4983230072969 + 3 ^ 40 * 382089 * 2
def baseEnd_382089 : Nat := 116263887286436034803147

theorem tailTrace_382089 : CollatzResearch.WordTrace tailWord_382089 prefixEnd_382089 116263887286436034803147 := by
  unfold tailWord_382089
  simp only [CollatzResearch.WordTrace]
  refine ⟨13935930712764283451045321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9290620475176188967363547 13935930712764283451045321)
  ·
    refine ⟨10451948034573212588283991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13935930712764283451045321 10451948034573212588283991)
    ·
      refine ⟨15677922051859818882425987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10451948034573212588283991 15677922051859818882425987)
      ·
        refine ⟨23516883077789728323638981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15677922051859818882425987 23516883077789728323638981)
        ·
          refine ⟨4409415577085574060682309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23516883077789728323638981 4409415577085574060682309)
          ·
            refine ⟨826765420703545136377933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4409415577085574060682309 826765420703545136377933)
            ·
              refine ⟨310037032763829426141725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 826765420703545136377933 310037032763829426141725)
              ·
                refine ⟨116263887286436034803147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310037032763829426141725 116263887286436034803147)
                ·
                  rfl

theorem cell19_382089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_382089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382089 prefixEnd_382089 := by exact prefixLift 382089
  have htrace : WordTrace (prefixWord ++ tailWord_382089) baseStart_382089 baseEnd_382089 := by
    simpa [prefixWord, tailWord_382089, baseEnd_382089] using wordTrace_append hprefix tailTrace_382089
  have hstable : (prefixWord ++ tailWord_382089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382089).length < 2 ^ (prefixWord ++ tailWord_382089).sum := by decide
  have hdescent : baseEnd_382089 < baseStart_382089 := by decide
  rcases family_descends (prefixWord ++ tailWord_382089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382144 : List Nat := [2, 1, 1, 2, 6, 2, 2, 3]
def baseStart_382144 : Nat := 118140960795 + 382144 * 2 ^ 59
def prefixEnd_382144 : Nat := 4983230072969 + 3 ^ 40 * 382144 * 2
def baseEnd_382144 : Nat := 116280622952212203580775

theorem tailTrace_382144 : CollatzResearch.WordTrace tailWord_382144 prefixEnd_382144 116280622952212203580775 := by
  unfold tailWord_382144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6968968363782513922148743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9291957818376685229531657 6968968363782513922148743)
  ·
    refine ⟨10453452545673770883223115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6968968363782513922148743 10453452545673770883223115)
    ·
      refine ⟨15680178818510656324834673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10453452545673770883223115 15680178818510656324834673)
      ·
        refine ⟨11760134113882992243626005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15680178818510656324834673 11760134113882992243626005)
        ·
          refine ⟨551256286588265261419969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11760134113882992243626005 551256286588265261419969)
          ·
            refine ⟨413442214941198946064977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551256286588265261419969 413442214941198946064977)
            ·
              refine ⟨310081661205899209548733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413442214941198946064977 310081661205899209548733)
              ·
                refine ⟨116280622952212203580775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310081661205899209548733 116280622952212203580775)
                ·
                  rfl

theorem cell19_382144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_382144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382144 prefixEnd_382144 := by exact prefixLift 382144
  have htrace : WordTrace (prefixWord ++ tailWord_382144) baseStart_382144 baseEnd_382144 := by
    simpa [prefixWord, tailWord_382144, baseEnd_382144] using wordTrace_append hprefix tailTrace_382144
  have hstable : (prefixWord ++ tailWord_382144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382144).length < 2 ^ (prefixWord ++ tailWord_382144).sum := by decide
  have hdescent : baseEnd_382144 < baseStart_382144 := by decide
  rcases family_descends (prefixWord ++ tailWord_382144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382165 : List Nat := [1, 3, 2, 4, 1, 3, 5]
def baseStart_382165 : Nat := 118140960795 + 382165 * 2 ^ 59
def prefixEnd_382165 : Nat := 4983230072969 + 3 ^ 40 * 382165 * 2
def baseEnd_382165 : Nat := 38762337644563459038017

theorem tailTrace_382165 : CollatzResearch.WordTrace tailWord_382165 prefixEnd_382165 38762337644563459038017 := by
  unfold tailWord_382165
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938702660488948430811949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9292468440325965620541299 13938702660488948430811949)
  ·
    refine ⟨5227013497683355661554481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13938702660488948430811949 5227013497683355661554481)
    ·
      refine ⟨3920260123262516746165861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5227013497683355661554481 3920260123262516746165861)
      ·
        refine ⟨735048773111721889906099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3920260123262516746165861 735048773111721889906099)
        ·
          refine ⟨1102573159667582834859149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735048773111721889906099 1102573159667582834859149)
          ·
            refine ⟨413464934875343563072181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1102573159667582834859149 413464934875343563072181)
            ·
              refine ⟨38762337644563459038017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 413464934875343563072181 38762337644563459038017)
              ·
                rfl

theorem cell19_382165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_382165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382165 prefixEnd_382165 := by exact prefixLift 382165
  have htrace : WordTrace (prefixWord ++ tailWord_382165) baseStart_382165 baseEnd_382165 := by
    simpa [prefixWord, tailWord_382165, baseEnd_382165] using wordTrace_append hprefix tailTrace_382165
  have hstable : (prefixWord ++ tailWord_382165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382165).length < 2 ^ (prefixWord ++ tailWord_382165).sum := by decide
  have hdescent : baseEnd_382165 < baseStart_382165 := by decide
  rcases family_descends (prefixWord ++ tailWord_382165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382186 : List Nat := [3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_382186 : Nat := 118140960795 + 382186 * 2 ^ 59
def prefixEnd_382186 : Nat := 4983230072969 + 3 ^ 40 * 382186 * 2
def baseEnd_382186 : Nat := 116293402915168550647327

theorem tailTrace_382186 : CollatzResearch.WordTrace tailWord_382186 prefixEnd_382186 116293402915168550647327 := by
  unfold tailWord_382186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484867148353217254331603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9292979062275246011550941 3484867148353217254331603)
  ·
    refine ⟨5227300722529825881497405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3484867148353217254331603 5227300722529825881497405)
    ·
      refine ⟨1960237770948684705561527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5227300722529825881497405 1960237770948684705561527)
      ·
        refine ⟨2940356656423027058342291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960237770948684705561527 2940356656423027058342291)
        ·
          refine ⟨4410534984634540587513437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940356656423027058342291 4410534984634540587513437)
          ·
            refine ⟨1653950619237952720317539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4410534984634540587513437 1653950619237952720317539)
            ·
              refine ⟨2480925928856929080476309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653950619237952720317539 2480925928856929080476309)
              ·
                refine ⟨116293402915168550647327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2480925928856929080476309 116293402915168550647327)
                ·
                  rfl

theorem cell19_382186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_382186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382186 prefixEnd_382186 := by exact prefixLift 382186
  have htrace : WordTrace (prefixWord ++ tailWord_382186) baseStart_382186 baseEnd_382186 := by
    simpa [prefixWord, tailWord_382186, baseEnd_382186] using wordTrace_append hprefix tailTrace_382186
  have hstable : (prefixWord ++ tailWord_382186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382186).length < 2 ^ (prefixWord ++ tailWord_382186).sum := by decide
  have hdescent : baseEnd_382186 < baseStart_382186 := by decide
  rcases family_descends (prefixWord ++ tailWord_382186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382239 : List Nat := [1, 1, 2, 4, 5, 1, 1, 4]
def baseStart_382239 : Nat := 118140960795 + 382239 * 2 ^ 59
def prefixEnd_382239 : Nat := 4983230072969 + 3 ^ 40 * 382239 * 2
def baseEnd_382239 : Nat := 116309530011280131469405

theorem tailTrace_382239 : CollatzResearch.WordTrace tailWord_382239 prefixEnd_382239 116309530011280131469405 := by
  unfold tailWord_382239
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941401662220859069005771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9294267774813906046003847 13941401662220859069005771)
  ·
    refine ⟨20912102493331288603508657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13941401662220859069005771 20912102493331288603508657)
    ·
      refine ⟨15684076869998466452631493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20912102493331288603508657 15684076869998466452631493)
      ·
        refine ⟨2940764413124712459868405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15684076869998466452631493 2940764413124712459868405)
        ·
          refine ⟨275696663730441793112663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2940764413124712459868405 275696663730441793112663)
          ·
            refine ⟨413544995595662689668995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275696663730441793112663 413544995595662689668995)
            ·
              refine ⟨620317493393494034503493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413544995595662689668995 620317493393494034503493)
              ·
                refine ⟨116309530011280131469405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620317493393494034503493 116309530011280131469405)
                ·
                  rfl

theorem cell19_382239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 4].length) (baseStart_382239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382239 prefixEnd_382239 := by exact prefixLift 382239
  have htrace : WordTrace (prefixWord ++ tailWord_382239) baseStart_382239 baseEnd_382239 := by
    simpa [prefixWord, tailWord_382239, baseEnd_382239] using wordTrace_append hprefix tailTrace_382239
  have hstable : (prefixWord ++ tailWord_382239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382239).length < 2 ^ (prefixWord ++ tailWord_382239).sum := by decide
  have hdescent : baseEnd_382239 < baseStart_382239 := by decide
  rcases family_descends (prefixWord ++ tailWord_382239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382243 : List Nat := [1, 1, 1, 4, 2, 3, 3, 4]
def baseStart_382243 : Nat := 118140960795 + 382243 * 2 ^ 59
def prefixEnd_382243 : Nat := 4983230072969 + 3 ^ 40 * 382243 * 2
def baseEnd_382243 : Nat := 116310747150609307380505

theorem tailTrace_382243 : CollatzResearch.WordTrace tailWord_382243 prefixEnd_382243 116310747150609307380505 := by
  unfold tailWord_382243
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941547554206367752151383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9294365036137578501434255 13941547554206367752151383)
  ·
    refine ⟨20912321331309551628227075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13941547554206367752151383 20912321331309551628227075)
    ·
      refine ⟨31368481996964327442340613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20912321331309551628227075 31368481996964327442340613)
      ·
        refine ⟨5881590374430811395438865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31368481996964327442340613 5881590374430811395438865)
        ·
          refine ⟨4411192780823108546579149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5881590374430811395438865 4411192780823108546579149)
          ·
            refine ⟨1654197292808665704967181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4411192780823108546579149 1654197292808665704967181)
            ·
              refine ⟨620323984803249639362693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1654197292808665704967181 620323984803249639362693)
              ·
                refine ⟨116310747150609307380505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620323984803249639362693 116310747150609307380505)
                ·
                  rfl

theorem cell19_382243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_382243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382243 prefixEnd_382243 := by exact prefixLift 382243
  have htrace : WordTrace (prefixWord ++ tailWord_382243) baseStart_382243 baseEnd_382243 := by
    simpa [prefixWord, tailWord_382243, baseEnd_382243] using wordTrace_append hprefix tailTrace_382243
  have hstable : (prefixWord ++ tailWord_382243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382243).length < 2 ^ (prefixWord ++ tailWord_382243).sum := by decide
  have hdescent : baseEnd_382243 < baseStart_382243 := by decide
  rcases family_descends (prefixWord ++ tailWord_382243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382317 : List Nat := [1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_382317 : Nat := 118140960795 + 382317 * 2 ^ 59
def prefixEnd_382317 : Nat := 4983230072969 + 3 ^ 40 * 382317 * 2
def baseEnd_382317 : Nat := 116333264228199061735859

theorem tailTrace_382317 : CollatzResearch.WordTrace tailWord_382317 prefixEnd_382317 116333264228199061735859 := by
  unfold tailWord_382317
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944246555938278390345205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9296164370625518926896803 13944246555938278390345205)
  ·
    refine ⟨1307273114619213599094863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13944246555938278390345205 1307273114619213599094863)
    ·
      refine ⟨1960909671928820398642295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307273114619213599094863 1960909671928820398642295)
      ·
        refine ⟨2941364507893230597963443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960909671928820398642295 2941364507893230597963443)
        ·
          refine ⟨4412046761839845896945165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941364507893230597963443 4412046761839845896945165)
          ·
            refine ⟨1654517535689942211354437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4412046761839845896945165 1654517535689942211354437)
            ·
              refine ⟨310222037941864164628957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1654517535689942211354437 310222037941864164628957)
              ·
                refine ⟨116333264228199061735859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310222037941864164628957 116333264228199061735859)
                ·
                  rfl

theorem cell19_382317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_382317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382317 prefixEnd_382317 := by exact prefixLift 382317
  have htrace : WordTrace (prefixWord ++ tailWord_382317) baseStart_382317 baseEnd_382317 := by
    simpa [prefixWord, tailWord_382317, baseEnd_382317] using wordTrace_append hprefix tailTrace_382317
  have hstable : (prefixWord ++ tailWord_382317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382317).length < 2 ^ (prefixWord ++ tailWord_382317).sum := by decide
  have hdescent : baseEnd_382317 < baseStart_382317 := by decide
  rcases family_descends (prefixWord ++ tailWord_382317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382412 : List Nat := [2, 2, 1, 4, 2, 3, 1, 4]
def baseStart_382412 : Nat := 118140960795 + 382412 * 2 ^ 59
def prefixEnd_382412 : Nat := 4983230072969 + 3 ^ 40 * 382412 * 2
def baseEnd_382412 : Nat := 116362171287266989624489

theorem tailTrace_382412 : CollatzResearch.WordTrace tailWord_382412 prefixEnd_382412 116362171287266989624489 := by
  unfold tailWord_382412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973855745297054807526745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9298474327062739743368993 6973855745297054807526745)
  ·
    refine ⟨5230391808972791105645059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6973855745297054807526745 5230391808972791105645059)
    ·
      refine ⟨7845587713459186658467589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230391808972791105645059 7845587713459186658467589)
      ·
        refine ⟨1471047696273597498462673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7845587713459186658467589 1471047696273597498462673)
        ·
          refine ⟨1103285772205198123847005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471047696273597498462673 1103285772205198123847005)
          ·
            refine ⟨413732164576949296442627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1103285772205198123847005 413732164576949296442627)
            ·
              refine ⟨620598246865423944663941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413732164576949296442627 620598246865423944663941)
              ·
                refine ⟨116362171287266989624489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620598246865423944663941 116362171287266989624489)
                ·
                  rfl

theorem cell19_382412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_382412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382412 prefixEnd_382412 := by exact prefixLift 382412
  have htrace : WordTrace (prefixWord ++ tailWord_382412) baseStart_382412 baseEnd_382412 := by
    simpa [prefixWord, tailWord_382412, baseEnd_382412] using wordTrace_append hprefix tailTrace_382412
  have hstable : (prefixWord ++ tailWord_382412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382412).length < 2 ^ (prefixWord ++ tailWord_382412).sum := by decide
  have hdescent : baseEnd_382412 < baseStart_382412 := by decide
  rcases family_descends (prefixWord ++ tailWord_382412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382414 : List Nat := [4, 1, 1, 1, 2, 1, 5, 4]
def baseStart_382414 : Nat := 118140960795 + 382414 * 2 ^ 59
def prefixEnd_382414 : Nat := 4983230072969 + 3 ^ 40 * 382414 * 2
def baseEnd_382414 : Nat := 116362779856931577580039

theorem tailTrace_382414 : CollatzResearch.WordTrace tailWord_382414 prefixEnd_382414 116362779856931577580039 := by
  unfold tailWord_382414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1743473054573357994578287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9298522957724575971084197 1743473054573357994578287)
  ·
    refine ⟨2615209581860036991867431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1743473054573357994578287 2615209581860036991867431)
    ·
      refine ⟨3922814372790055487801147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615209581860036991867431 3922814372790055487801147)
      ·
        refine ⟨5884221559185083231701721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3922814372790055487801147 5884221559185083231701721)
        ·
          refine ⟨4413166169388812423776291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5884221559185083231701721 4413166169388812423776291)
          ·
            refine ⟨6619749254083218635664437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4413166169388812423776291 6619749254083218635664437)
            ·
              refine ⟨620601492570301747093541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6619749254083218635664437 620601492570301747093541)
              ·
                refine ⟨116362779856931577580039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620601492570301747093541 116362779856931577580039)
                ·
                  rfl

theorem cell19_382414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_382414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382414 prefixEnd_382414 := by exact prefixLift 382414
  have htrace : WordTrace (prefixWord ++ tailWord_382414) baseStart_382414 baseEnd_382414 := by
    simpa [prefixWord, tailWord_382414, baseEnd_382414] using wordTrace_append hprefix tailTrace_382414
  have hstable : (prefixWord ++ tailWord_382414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382414).length < 2 ^ (prefixWord ++ tailWord_382414).sum := by decide
  have hdescent : baseEnd_382414 < baseStart_382414 := by decide
  rcases family_descends (prefixWord ++ tailWord_382414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382473 : List Nat := [1, 2, 1, 1, 3, 1, 4, 6]
def baseStart_382473 : Nat := 118140960795 + 382473 * 2 ^ 59
def prefixEnd_382473 : Nat := 4983230072969 + 3 ^ 40 * 382473 * 2
def baseEnd_382473 : Nat := 116380732662036922268767

theorem tailTrace_382473 : CollatzResearch.WordTrace tailWord_382473 prefixEnd_382473 116380732662036922268767 := by
  unfold tailWord_382473
  simp only [CollatzResearch.WordTrace]
  refine ⟨13949936343373117033024073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9299957562248744688682715 13949936343373117033024073)
  ·
    refine ⟨10462452257529837774768055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13949936343373117033024073 10462452257529837774768055)
    ·
      refine ⟨15693678386294756662152083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10462452257529837774768055 15693678386294756662152083)
      ·
        refine ⟨23540517579442134993228125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15693678386294756662152083 23540517579442134993228125)
        ·
          refine ⟨8827694092290800622460547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23540517579442134993228125 8827694092290800622460547)
          ·
            refine ⟨13241541138436200933690821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827694092290800622460547 13241541138436200933690821)
            ·
              refine ⟨2482788963456787675067029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13241541138436200933690821 2482788963456787675067029)
              ·
                refine ⟨116380732662036922268767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2482788963456787675067029 116380732662036922268767)
                ·
                  rfl

theorem cell19_382473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_382473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382473 prefixEnd_382473 := by exact prefixLift 382473
  have htrace : WordTrace (prefixWord ++ tailWord_382473) baseStart_382473 baseEnd_382473 := by
    simpa [prefixWord, tailWord_382473, baseEnd_382473] using wordTrace_append hprefix tailTrace_382473
  have hstable : (prefixWord ++ tailWord_382473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382473).length < 2 ^ (prefixWord ++ tailWord_382473).sum := by decide
  have hdescent : baseEnd_382473 < baseStart_382473 := by decide
  rcases family_descends (prefixWord ++ tailWord_382473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382484 : List Nat := [2, 4, 3, 1, 2, 2, 2, 3]
def baseStart_382484 : Nat := 118140960795 + 382484 * 2 ^ 59
def prefixEnd_382484 : Nat := 4983230072969 + 3 ^ 40 * 382484 * 2
def baseEnd_382484 : Nat := 116384079795192156024293

theorem tailTrace_382484 : CollatzResearch.WordTrace tailWord_382484 prefixEnd_382484 116384079795192156024293 := by
  unfold tailWord_382484
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975168773166632955837253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9300225030888843941116337 6975168773166632955837253)
  ·
    refine ⟨1307844144968743679219485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6975168773166632955837253 1307844144968743679219485)
    ·
      refine ⟨490441554363278879707307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1307844144968743679219485 490441554363278879707307)
      ·
        refine ⟨735662331544918319560961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 490441554363278879707307 735662331544918319560961)
        ·
          refine ⟨551746748658688739670721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735662331544918319560961 551746748658688739670721)
          ·
            refine ⟨413810061494016554753041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551746748658688739670721 413810061494016554753041)
            ·
              refine ⟨310357546120512416064781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413810061494016554753041 310357546120512416064781)
              ·
                refine ⟨116384079795192156024293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310357546120512416064781 116384079795192156024293)
                ·
                  rfl

theorem cell19_382484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_382484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382484 prefixEnd_382484 := by exact prefixLift 382484
  have htrace : WordTrace (prefixWord ++ tailWord_382484) baseStart_382484 baseEnd_382484 := by
    simpa [prefixWord, tailWord_382484, baseEnd_382484] using wordTrace_append hprefix tailTrace_382484
  have hstable : (prefixWord ++ tailWord_382484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382484).length < 2 ^ (prefixWord ++ tailWord_382484).sum := by decide
  have hdescent : baseEnd_382484 < baseStart_382484 := by decide
  rcases family_descends (prefixWord ++ tailWord_382484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382600 : List Nat := [2, 1, 3, 5, 1, 1, 3, 3]
def baseStart_382600 : Nat := 118140960795 + 382600 * 2 ^ 59
def prefixEnd_382600 : Nat := 4983230072969 + 3 ^ 40 * 382600 * 2
def baseEnd_382600 : Nat := 116419376835738257446199

theorem tailTrace_382600 : CollatzResearch.WordTrace tailWord_382600 prefixEnd_382600 116419376835738257446199 := by
  unfold tailWord_382600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977284206956508861448627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9303045609275345148598169 6977284206956508861448627)
  ·
    refine ⟨10465926310434763292172941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6977284206956508861448627 10465926310434763292172941)
    ·
      refine ⟨3924722366413036234564853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10465926310434763292172941 3924722366413036234564853)
      ·
        refine ⟨367942721851222146990455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3924722366413036234564853 367942721851222146990455)
        ·
          refine ⟨551914082776833220485683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367942721851222146990455 551914082776833220485683)
          ·
            refine ⟨827871124165249830728525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551914082776833220485683 827871124165249830728525)
            ·
              refine ⟨310451671561968686523197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827871124165249830728525 310451671561968686523197)
              ·
                refine ⟨116419376835738257446199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310451671561968686523197 116419376835738257446199)
                ·
                  rfl

theorem cell19_382600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_382600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382600 prefixEnd_382600 := by exact prefixLift 382600
  have htrace : WordTrace (prefixWord ++ tailWord_382600) baseStart_382600 baseEnd_382600 := by
    simpa [prefixWord, tailWord_382600, baseEnd_382600] using wordTrace_append hprefix tailTrace_382600
  have hstable : (prefixWord ++ tailWord_382600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382600).length < 2 ^ (prefixWord ++ tailWord_382600).sum := by decide
  have hdescent : baseEnd_382600 < baseStart_382600 := by decide
  rcases family_descends (prefixWord ++ tailWord_382600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382602 : List Nat := [3, 1, 2, 3, 2, 2, 3, 3]
def baseStart_382602 : Nat := 118140960795 + 382602 * 2 ^ 59
def prefixEnd_382602 : Nat := 4983230072969 + 3 ^ 40 * 382602 * 2
def baseEnd_382602 : Nat := 116419985405402845401749

theorem tailTrace_382602 : CollatzResearch.WordTrace tailWord_382602 prefixEnd_382602 116419985405402845401749 := by
  unfold tailWord_382602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3488660339976443016117515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9303094239937181376313373 3488660339976443016117515)
  ·
    refine ⟨5232990509964664524176273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3488660339976443016117515 5232990509964664524176273)
    ·
      refine ⟨3924742882473498393132205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5232990509964664524176273 3924742882473498393132205)
      ·
        refine ⟨1471778580927561897424577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3924742882473498393132205 1471778580927561897424577)
        ·
          refine ⟨1103833935695671423068433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471778580927561897424577 1103833935695671423068433)
          ·
            refine ⟨827875451771753567301325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1103833935695671423068433 827875451771753567301325)
            ·
              refine ⟨310453294414407587737997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827875451771753567301325 310453294414407587737997)
              ·
                refine ⟨116419985405402845401749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310453294414407587737997 116419985405402845401749)
                ·
                  rfl

theorem cell19_382602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_382602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382602 prefixEnd_382602 := by exact prefixLift 382602
  have htrace : WordTrace (prefixWord ++ tailWord_382602) baseStart_382602 baseEnd_382602 := by
    simpa [prefixWord, tailWord_382602, baseEnd_382602] using wordTrace_append hprefix tailTrace_382602
  have hstable : (prefixWord ++ tailWord_382602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382602).length < 2 ^ (prefixWord ++ tailWord_382602).sum := by decide
  have hdescent : baseEnd_382602 < baseStart_382602 := by decide
  rcases family_descends (prefixWord ++ tailWord_382602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382604 : List Nat := [2, 2, 1, 2, 1, 1, 7, 3]
def baseStart_382604 : Nat := 118140960795 + 382604 * 2 ^ 59
def prefixEnd_382604 : Nat := 4983230072969 + 3 ^ 40 * 382604 * 2
def baseEnd_382604 : Nat := 116420593975067433357299

theorem tailTrace_382604 : CollatzResearch.WordTrace tailWord_382604 prefixEnd_382604 116420593975067433357299 := by
  unfold tailWord_382604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977357152949263203021433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9303142870599017604028577 6977357152949263203021433)
  ·
    refine ⟨5233017864711947402266075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6977357152949263203021433 5233017864711947402266075)
    ·
      refine ⟨7849526797067921103399113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233017864711947402266075 7849526797067921103399113)
      ·
        refine ⟨5887145097800940827549335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7849526797067921103399113 5887145097800940827549335)
        ·
          refine ⟨8830717646701411241324003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5887145097800940827549335 8830717646701411241324003)
          ·
            refine ⟨13246076470052116861986005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8830717646701411241324003 13246076470052116861986005)
            ·
              refine ⟨310454917266846488952797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13246076470052116861986005 310454917266846488952797)
              ·
                refine ⟨116420593975067433357299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310454917266846488952797 116420593975067433357299)
                ·
                  rfl

theorem cell19_382604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_382604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382604 prefixEnd_382604 := by exact prefixLift 382604
  have htrace : WordTrace (prefixWord ++ tailWord_382604) baseStart_382604 baseEnd_382604 := by
    simpa [prefixWord, tailWord_382604, baseEnd_382604] using wordTrace_append hprefix tailTrace_382604
  have hstable : (prefixWord ++ tailWord_382604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382604).length < 2 ^ (prefixWord ++ tailWord_382604).sum := by decide
  have hdescent : baseEnd_382604 < baseStart_382604 := by decide
  rcases family_descends (prefixWord ++ tailWord_382604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382663 : List Nat := [1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_382663 : Nat := 118140960795 + 382663 * 2 ^ 59
def prefixEnd_382663 : Nat := 4983230072969 + 3 ^ 40 * 382663 * 2
def baseEnd_382663 : Nat := 116438546780172778046027

theorem tailTrace_382663 : CollatzResearch.WordTrace tailWord_382663 prefixEnd_382663 116438546780172778046027 := by
  unfold tailWord_382663
  simp only [CollatzResearch.WordTrace]
  refine ⟨13956866212684779482440643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9304577475123186321627095 13956866212684779482440643)
  ·
    refine ⟨20935299319027169223660965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13956866212684779482440643 20935299319027169223660965)
    ·
      refine ⟨3925368622317594229436431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20935299319027169223660965 3925368622317594229436431)
      ·
        refine ⟨5888052933476391344154647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925368622317594229436431 5888052933476391344154647)
        ·
          refine ⟨8832079400214587016231971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5888052933476391344154647 8832079400214587016231971)
          ·
            refine ⟨13248119100321880524347957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8832079400214587016231971 13248119100321880524347957)
            ·
              refine ⟨1242011165655176299157621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13248119100321880524347957 1242011165655176299157621)
              ·
                refine ⟨116438546780172778046027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1242011165655176299157621 116438546780172778046027)
                ·
                  rfl

theorem cell19_382663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_382663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382663 prefixEnd_382663 := by exact prefixLift 382663
  have htrace : WordTrace (prefixWord ++ tailWord_382663) baseStart_382663 baseEnd_382663 := by
    simpa [prefixWord, tailWord_382663, baseEnd_382663] using wordTrace_append hprefix tailTrace_382663
  have hstable : (prefixWord ++ tailWord_382663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382663).length < 2 ^ (prefixWord ++ tailWord_382663).sum := by decide
  have hdescent : baseEnd_382663 < baseStart_382663 := by decide
  rcases family_descends (prefixWord ++ tailWord_382663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382682 : List Nat := [3, 1, 1, 2, 2, 3, 7]
def baseStart_382682 : Nat := 118140960795 + 382682 * 2 ^ 59
def prefixEnd_382682 : Nat := 4983230072969 + 3 ^ 40 * 382682 * 2
def baseEnd_382682 : Nat := 38814776063995454541251

theorem tailTrace_382682 : CollatzResearch.WordTrace tailWord_382682 prefixEnd_382682 38814776063995454541251 := by
  unfold tailWord_382682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489389799903986431845575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9305039466410630484921533 3489389799903986431845575)
  ·
    refine ⟨5234084699855979647768363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3489389799903986431845575 5234084699855979647768363)
    ·
      refine ⟨7851127049783969471652545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234084699855979647768363 7851127049783969471652545)
      ·
        refine ⟨5888345287337977103739409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7851127049783969471652545 5888345287337977103739409)
        ·
          refine ⟨4416258965503482827804557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5888345287337977103739409 4416258965503482827804557)
          ·
            refine ⟨1656097112063806060426709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4416258965503482827804557 1656097112063806060426709)
            ·
              refine ⟨38814776063995454541251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1656097112063806060426709 38814776063995454541251)
              ·
                rfl

theorem cell19_382682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 7].length) (baseStart_382682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382682 prefixEnd_382682 := by exact prefixLift 382682
  have htrace : WordTrace (prefixWord ++ tailWord_382682) baseStart_382682 baseEnd_382682 := by
    simpa [prefixWord, tailWord_382682, baseEnd_382682] using wordTrace_append hprefix tailTrace_382682
  have hstable : (prefixWord ++ tailWord_382682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382682).length < 2 ^ (prefixWord ++ tailWord_382682).sum := by decide
  have hdescent : baseEnd_382682 < baseStart_382682 := by decide
  rcases family_descends (prefixWord ++ tailWord_382682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382733 : List Nat := [1, 7, 2, 1, 8]
def baseStart_382733 : Nat := 118140960795 + 382733 * 2 ^ 59
def prefixEnd_382733 : Nat := 4983230072969 + 3 ^ 40 * 382733 * 2
def baseEnd_382733 : Nat := 4313327656238272462603

theorem tailTrace_382733 : CollatzResearch.WordTrace tailWord_382733 prefixEnd_382733 4313327656238272462603 := by
  unfold tailWord_382733
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959419322431181437488853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9306279548287454291659235 13959419322431181437488853)
  ·
    refine ⟨327173890369480814941145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13959419322431181437488853 327173890369480814941145)
    ·
      refine ⟨245380417777110611205859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 327173890369480814941145 245380417777110611205859)
      ·
        refine ⟨368070626665665916808789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245380417777110611205859 368070626665665916808789)
        ·
          refine ⟨4313327656238272462603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 368070626665665916808789 4313327656238272462603)
          ·
            rfl

theorem cell19_382733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 8].length) (baseStart_382733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382733 prefixEnd_382733 := by exact prefixLift 382733
  have htrace : WordTrace (prefixWord ++ tailWord_382733) baseStart_382733 baseEnd_382733 := by
    simpa [prefixWord, tailWord_382733, baseEnd_382733] using wordTrace_append hprefix tailTrace_382733
  have hstable : (prefixWord ++ tailWord_382733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382733).length < 2 ^ (prefixWord ++ tailWord_382733).sum := by decide
  have hdescent : baseEnd_382733 < baseStart_382733 := by decide
  rcases family_descends (prefixWord ++ tailWord_382733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382750 : List Nat := [4, 3, 2, 2, 1, 2, 1, 4]
def baseStart_382750 : Nat := 118140960795 + 382750 * 2 ^ 59
def prefixEnd_382750 : Nat := 4983230072969 + 3 ^ 40 * 382750 * 2
def baseEnd_382750 : Nat := 116465019560582354112457

theorem tailTrace_382750 : CollatzResearch.WordTrace tailWord_382750 prefixEnd_382750 116465019560582354112457 := by
  unfold tailWord_382750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745004920421199167607213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9306692908913062227238469 1745004920421199167607213)
  ·
    refine ⟨654376845157949687852705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1745004920421199167607213 654376845157949687852705)
    ·
      refine ⟨490782633868462265889529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 654376845157949687852705 490782633868462265889529)
      ·
        refine ⟨368086975401346699417147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490782633868462265889529 368086975401346699417147)
        ·
          refine ⟨552130463102020049125721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368086975401346699417147 552130463102020049125721)
          ·
            refine ⟨414097847326515036844291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552130463102020049125721 414097847326515036844291)
            ·
              refine ⟨621146770989772555266437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414097847326515036844291 621146770989772555266437)
              ·
                refine ⟨116465019560582354112457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621146770989772555266437 116465019560582354112457)
                ·
                  rfl

theorem cell19_382750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_382750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382750 prefixEnd_382750 := by exact prefixLift 382750
  have htrace : WordTrace (prefixWord ++ tailWord_382750) baseStart_382750 baseEnd_382750 := by
    simpa [prefixWord, tailWord_382750, baseEnd_382750] using wordTrace_append hprefix tailTrace_382750
  have hstable : (prefixWord ++ tailWord_382750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382750).length < 2 ^ (prefixWord ++ tailWord_382750).sum := by decide
  have hdescent : baseEnd_382750 < baseStart_382750 := by decide
  rcases family_descends (prefixWord ++ tailWord_382750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382756 : List Nat := [2, 3, 1, 3, 2, 1, 3, 4]
def baseStart_382756 : Nat := 118140960795 + 382756 * 2 ^ 59
def prefixEnd_382756 : Nat := 4983230072969 + 3 ^ 40 * 382756 * 2
def baseEnd_382756 : Nat := 116466845269576117979107

theorem tailTrace_382756 : CollatzResearch.WordTrace tailWord_382756 prefixEnd_382756 116466845269576117979107 := by
  unfold tailWord_382756
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980129100673928182788061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9306838800898570910384081 6980129100673928182788061)
  ·
    refine ⟨2617548412752723068545523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6980129100673928182788061 2617548412752723068545523)
    ·
      refine ⟨3926322619129084602818285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2617548412752723068545523 3926322619129084602818285)
      ·
        refine ⟨1472370982173406726056857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3926322619129084602818285 1472370982173406726056857)
        ·
          refine ⟨1104278236630055044542643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1472370982173406726056857 1104278236630055044542643)
          ·
            refine ⟨1656417354945082566813965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104278236630055044542643 1656417354945082566813965)
            ·
              refine ⟨621156508104405962555237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1656417354945082566813965 621156508104405962555237)
              ·
                refine ⟨116466845269576117979107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621156508104405962555237 116466845269576117979107)
                ·
                  rfl

theorem cell19_382756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_382756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382756 prefixEnd_382756 := by exact prefixLift 382756
  have htrace : WordTrace (prefixWord ++ tailWord_382756) baseStart_382756 baseEnd_382756 := by
    simpa [prefixWord, tailWord_382756, baseEnd_382756] using wordTrace_append hprefix tailTrace_382756
  have hstable : (prefixWord ++ tailWord_382756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382756).length < 2 ^ (prefixWord ++ tailWord_382756).sum := by decide
  have hdescent : baseEnd_382756 < baseStart_382756 := by decide
  rcases family_descends (prefixWord ++ tailWord_382756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382773 : List Nat := [1, 3, 3, 1, 4, 1, 3, 3]
def baseStart_382773 : Nat := 118140960795 + 382773 * 2 ^ 59
def prefixEnd_382773 : Nat := 4983230072969 + 3 ^ 40 * 382773 * 2
def baseEnd_382773 : Nat := 116472018111725115601283

theorem tailTrace_382773 : CollatzResearch.WordTrace tailWord_382773 prefixEnd_382773 116472018111725115601283 := by
  unfold tailWord_382773
  simp only [CollatzResearch.WordTrace]
  refine ⟨13960878242286268268944973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9307252161524178845963315 13960878242286268268944973)
  ·
    refine ⟨5235329340857350600854365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13960878242286268268944973 5235329340857350600854365)
    ·
      refine ⟨1963248502821506475320387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5235329340857350600854365 1963248502821506475320387)
      ·
        refine ⟨2944872754232259712980581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963248502821506475320387 2944872754232259712980581)
        ·
          refine ⟨552163641418548696183859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2944872754232259712980581 552163641418548696183859)
          ·
            refine ⟨828245462127823044275789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552163641418548696183859 828245462127823044275789)
            ·
              refine ⟨310592048297933641603421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828245462127823044275789 310592048297933641603421)
              ·
                refine ⟨116472018111725115601283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310592048297933641603421 116472018111725115601283)
                ·
                  rfl

theorem cell19_382773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_382773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382773 prefixEnd_382773 := by exact prefixLift 382773
  have htrace : WordTrace (prefixWord ++ tailWord_382773) baseStart_382773 baseEnd_382773 := by
    simpa [prefixWord, tailWord_382773, baseEnd_382773] using wordTrace_append hprefix tailTrace_382773
  have hstable : (prefixWord ++ tailWord_382773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382773).length < 2 ^ (prefixWord ++ tailWord_382773).sum := by decide
  have hdescent : baseEnd_382773 < baseStart_382773 := by decide
  rcases family_descends (prefixWord ++ tailWord_382773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382826 : List Nat := [3, 1, 3, 4, 2, 1, 2, 3]
def baseStart_382826 : Nat := 118140960795 + 382826 * 2 ^ 59
def prefixEnd_382826 : Nat := 4983230072969 + 3 ^ 40 * 382826 * 2
def baseEnd_382826 : Nat := 116488145207836696423361

theorem tailTrace_382826 : CollatzResearch.WordTrace tailWord_382826 prefixEnd_382826 116488145207836696423361 := by
  unfold tailWord_382826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3490702827773564580156083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9308540874062838880416221 3490702827773564580156083)
  ·
    refine ⟨5236054241660346870234125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3490702827773564580156083 5236054241660346870234125)
    ·
      refine ⟨1963520340622630076337797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5236054241660346870234125 1963520340622630076337797)
      ·
        refine ⟨368160063866743139313337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1963520340622630076337797 368160063866743139313337)
        ·
          refine ⟨276120047900057354485003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 368160063866743139313337 276120047900057354485003)
          ·
            refine ⟨414180071850086031727505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276120047900057354485003 414180071850086031727505)
            ·
              refine ⟨310635053887564523795629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414180071850086031727505 310635053887564523795629)
              ·
                refine ⟨116488145207836696423361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310635053887564523795629 116488145207836696423361)
                ·
                  rfl

theorem cell19_382826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_382826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382826 prefixEnd_382826 := by exact prefixLift 382826
  have htrace : WordTrace (prefixWord ++ tailWord_382826) baseStart_382826 baseEnd_382826 := by
    simpa [prefixWord, tailWord_382826, baseEnd_382826] using wordTrace_append hprefix tailTrace_382826
  have hstable : (prefixWord ++ tailWord_382826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382826).length < 2 ^ (prefixWord ++ tailWord_382826).sum := by decide
  have hdescent : baseEnd_382826 < baseStart_382826 := by decide
  rcases family_descends (prefixWord ++ tailWord_382826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382830 : List Nat := [4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_382830 : Nat := 118140960795 + 382830 * 2 ^ 59
def prefixEnd_382830 : Nat := 4983230072969 + 3 ^ 40 * 382830 * 2
def baseEnd_382830 : Nat := 116489362347165872334461

theorem tailTrace_382830 : CollatzResearch.WordTrace tailWord_382830 prefixEnd_382830 116489362347165872334461 := by
  unfold tailWord_382830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745369650384970875471243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9308638135386511335846629 1745369650384970875471243)
  ·
    refine ⟨2618054475577456313206865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745369650384970875471243 2618054475577456313206865)
    ·
      refine ⟨1963540856683092234905149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2618054475577456313206865 1963540856683092234905149)
      ·
        refine ⟨736327821256159588089431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1963540856683092234905149 736327821256159588089431)
        ·
          refine ⟨1104491731884239382134147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736327821256159588089431 1104491731884239382134147)
          ·
            refine ⟨1656737597826359073201221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104491731884239382134147 1656737597826359073201221)
            ·
              refine ⟨310638299592442326225229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1656737597826359073201221 310638299592442326225229)
              ·
                refine ⟨116489362347165872334461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310638299592442326225229 116489362347165872334461)
                ·
                  rfl

theorem cell19_382830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_382830 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382830 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382830 prefixEnd_382830 := by exact prefixLift 382830
  have htrace : WordTrace (prefixWord ++ tailWord_382830) baseStart_382830 baseEnd_382830 := by
    simpa [prefixWord, tailWord_382830, baseEnd_382830] using wordTrace_append hprefix tailTrace_382830
  have hstable : (prefixWord ++ tailWord_382830).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382830).length < 2 ^ (prefixWord ++ tailWord_382830).sum := by decide
  have hdescent : baseEnd_382830 < baseStart_382830 := by decide
  rcases family_descends (prefixWord ++ tailWord_382830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382849 : List Nat := [1, 2, 4, 4, 1, 2, 5]
def baseStart_382849 : Nat := 118140960795 + 382849 * 2 ^ 59
def prefixEnd_382849 : Nat := 4983230072969 + 3 ^ 40 * 382849 * 2
def baseEnd_382849 : Nat := 38831714586326485970729

theorem tailTrace_382849 : CollatzResearch.WordTrace tailWord_382849 prefixEnd_382849 38831714586326485970729 := by
  unfold tailWord_382849
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963650190010933248711601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9309100126673955499141067 13963650190010933248711601)
  ·
    refine ⟨10472737642508199936533701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13963650190010933248711601 10472737642508199936533701)
    ·
      refine ⟨1963638307970287488100069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10472737642508199936533701 1963638307970287488100069)
      ·
        refine ⟨368182182744428904018763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1963638307970287488100069 368182182744428904018763)
        ·
          refine ⟨552273274116643356028145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368182182744428904018763 552273274116643356028145)
          ·
            refine ⟨414204955587482517021109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552273274116643356028145 414204955587482517021109)
            ·
              refine ⟨38831714586326485970729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414204955587482517021109 38831714586326485970729)
              ·
                rfl

theorem cell19_382849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_382849 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382849 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382849 prefixEnd_382849 := by exact prefixLift 382849
  have htrace : WordTrace (prefixWord ++ tailWord_382849) baseStart_382849 baseEnd_382849 := by
    simpa [prefixWord, tailWord_382849, baseEnd_382849] using wordTrace_append hprefix tailTrace_382849
  have hstable : (prefixWord ++ tailWord_382849).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382849).length < 2 ^ (prefixWord ++ tailWord_382849).sum := by decide
  have hdescent : baseEnd_382849 < baseStart_382849 := by decide
  rcases family_descends (prefixWord ++ tailWord_382849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382908 : List Nat := [2, 2, 2, 5, 1, 7]
def baseStart_382908 : Nat := 118140960795 + 382908 * 2 ^ 59
def prefixEnd_382908 : Nat := 4983230072969 + 3 ^ 40 * 382908 * 2
def baseEnd_382908 : Nat := 12945899618231644733435

theorem tailTrace_382908 : CollatzResearch.WordTrace tailWord_382908 prefixEnd_382908 12945899618231644733435 := by
  unfold tailWord_382908
  simp only [CollatzResearch.WordTrace]
  refine ⟨6982901048398593162554689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9310534731198124216739585 6982901048398593162554689)
  ·
    refine ⟨5237175786298944871916017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6982901048398593162554689 5237175786298944871916017)
    ·
      refine ⟨3927881839724208653937013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5237175786298944871916017 3927881839724208653937013)
      ·
        refine ⟨368238922474144561306595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3927881839724208653937013 368238922474144561306595)
        ·
          refine ⟨552358383711216841959893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368238922474144561306595 552358383711216841959893)
          ·
            refine ⟨12945899618231644733435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 552358383711216841959893 12945899618231644733435)
            ·
              rfl

theorem cell19_382908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 7].length) (baseStart_382908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382908 prefixEnd_382908 := by exact prefixLift 382908
  have htrace : WordTrace (prefixWord ++ tailWord_382908) baseStart_382908 baseEnd_382908 := by
    simpa [prefixWord, tailWord_382908, baseEnd_382908] using wordTrace_append hprefix tailTrace_382908
  have hstable : (prefixWord ++ tailWord_382908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382908).length < 2 ^ (prefixWord ++ tailWord_382908).sum := by decide
  have hdescent : baseEnd_382908 < baseStart_382908 := by decide
  rcases family_descends (prefixWord ++ tailWord_382908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382910 : List Nat := [4, 2, 1, 1, 1, 10]
def baseStart_382910 : Nat := 118140960795 + 382910 * 2 ^ 59
def prefixEnd_382910 : Nat := 4983230072969 + 3 ^ 40 * 382910 * 2
def baseEnd_382910 : Nat := 12945967237083265617385

theorem tailTrace_382910 : CollatzResearch.WordTrace tailWord_382910 prefixEnd_382910 12945967237083265617385 := by
  unfold tailWord_382910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745734380348742583335273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9310583361859960444454789 1745734380348742583335273)
  ·
    refine ⟨1309300785261556937501455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1745734380348742583335273 1309300785261556937501455)
    ·
      refine ⟨1963951177892335406252183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309300785261556937501455 1963951177892335406252183)
      ·
        refine ⟨2945926766838503109378275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963951177892335406252183 2945926766838503109378275)
        ·
          refine ⟨4418890150257754664067413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2945926766838503109378275 4418890150257754664067413)
          ·
            refine ⟨12945967237083265617385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4418890150257754664067413 12945967237083265617385)
            ·
              rfl

theorem cell19_382910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 10].length) (baseStart_382910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382910 prefixEnd_382910 := by exact prefixLift 382910
  have htrace : WordTrace (prefixWord ++ tailWord_382910) baseStart_382910 baseEnd_382910 := by
    simpa [prefixWord, tailWord_382910, baseEnd_382910] using wordTrace_append hprefix tailTrace_382910
  have hstable : (prefixWord ++ tailWord_382910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382910).length < 2 ^ (prefixWord ++ tailWord_382910).sum := by decide
  have hdescent : baseEnd_382910 < baseStart_382910 := by decide
  rcases family_descends (prefixWord ++ tailWord_382910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382940 : List Nat := [2, 2, 6, 1, 1, 1, 3, 3]
def baseStart_382940 : Nat := 118140960795 + 382940 * 2 ^ 59
def prefixEnd_382940 : Nat := 4983230072969 + 3 ^ 40 * 382940 * 2
def baseEnd_382940 : Nat := 116522833678718209889717

theorem tailTrace_382940 : CollatzResearch.WordTrace tailWord_382940 prefixEnd_382940 116522833678718209889717 := by
  unfold tailWord_382940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6983484616340627895137137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9311312821787503860182849 6983484616340627895137137)
  ·
    refine ⟨5237613462255470921352853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6983484616340627895137137 5237613462255470921352853)
    ·
      refine ⟨245513131043225199438415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5237613462255470921352853 245513131043225199438415)
      ·
        refine ⟨368269696564837799157623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245513131043225199438415 368269696564837799157623)
        ·
          refine ⟨552404544847256698736435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368269696564837799157623 552404544847256698736435)
          ·
            refine ⟨828606817270885048104653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552404544847256698736435 828606817270885048104653)
            ·
              refine ⟨310727556476581893039245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828606817270885048104653 310727556476581893039245)
              ·
                refine ⟨116522833678718209889717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310727556476581893039245 116522833678718209889717)
                ·
                  rfl

theorem cell19_382940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 3].length) (baseStart_382940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382940 prefixEnd_382940 := by exact prefixLift 382940
  have htrace : WordTrace (prefixWord ++ tailWord_382940) baseStart_382940 baseEnd_382940 := by
    simpa [prefixWord, tailWord_382940, baseEnd_382940] using wordTrace_append hprefix tailTrace_382940
  have hstable : (prefixWord ++ tailWord_382940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382940).length < 2 ^ (prefixWord ++ tailWord_382940).sum := by decide
  have hdescent : baseEnd_382940 < baseStart_382940 := by decide
  rcases family_descends (prefixWord ++ tailWord_382940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382999 : List Nat := [1, 1, 3, 5, 3, 1, 2, 3]
def baseStart_382999 : Nat := 118140960795 + 382999 * 2 ^ 59
def prefixEnd_382999 : Nat := 4983230072969 + 3 ^ 40 * 382999 * 2
def baseEnd_382999 : Nat := 116540786483823554578445

theorem tailTrace_382999 : CollatzResearch.WordTrace tailWord_382999 prefixEnd_382999 116540786483823554578445 := by
  unfold tailWord_382999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13969121139467508866672051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9312747426311672577781367 13969121139467508866672051)
  ·
    refine ⟨20953681709201263300008077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13969121139467508866672051 20953681709201263300008077)
    ·
      refine ⟨7857630640950473737503029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20953681709201263300008077 7857630640950473737503029)
      ·
        refine ⟨736652872589106912890909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7857630640950473737503029 736652872589106912890909)
        ·
          refine ⟨276244827220915092334091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736652872589106912890909 276244827220915092334091)
          ·
            refine ⟨414367240831372638501137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276244827220915092334091 414367240831372638501137)
            ·
              refine ⟨310775430623529478875853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414367240831372638501137 310775430623529478875853)
              ·
                refine ⟨116540786483823554578445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310775430623529478875853 116540786483823554578445)
                ·
                  rfl

theorem cell19_382999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 3].length) (baseStart_382999 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_382999 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_382999 prefixEnd_382999 := by exact prefixLift 382999
  have htrace : WordTrace (prefixWord ++ tailWord_382999) baseStart_382999 baseEnd_382999 := by
    simpa [prefixWord, tailWord_382999, baseEnd_382999] using wordTrace_append hprefix tailTrace_382999
  have hstable : (prefixWord ++ tailWord_382999).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382999).length < 2 ^ (prefixWord ++ tailWord_382999).sum := by decide
  have hdescent : baseEnd_382999 < baseStart_382999 := by decide
  rcases family_descends (prefixWord ++ tailWord_382999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383022 : List Nat := [4, 1, 3, 1, 1, 4, 5]
def baseStart_383022 : Nat := 118140960795 + 383022 * 2 ^ 59
def prefixEnd_383022 : Nat := 4983230072969 + 3 ^ 40 * 383022 * 2
def baseEnd_383022 : Nat := 38849261678322105355757

theorem tailTrace_383022 : CollatzResearch.WordTrace tailWord_383022 prefixEnd_383022 38849261678322105355757 := by
  unfold tailWord_383022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1746245002298022974344915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9313306678922789196506213 1746245002298022974344915)
  ·
    refine ⟨2619367503447034461517373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1746245002298022974344915 2619367503447034461517373)
    ·
      refine ⟨982262813792637923069015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2619367503447034461517373 982262813792637923069015)
      ·
        refine ⟨1473394220688956884603523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982262813792637923069015 1473394220688956884603523)
        ·
          refine ⟨2210091331033435326905285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473394220688956884603523 2210091331033435326905285)
          ·
            refine ⟨414392124568769123794741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2210091331033435326905285 414392124568769123794741)
            ·
              refine ⟨38849261678322105355757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414392124568769123794741 38849261678322105355757)
              ·
                rfl

theorem cell19_383022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 5].length) (baseStart_383022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383022 prefixEnd_383022 := by exact prefixLift 383022
  have htrace : WordTrace (prefixWord ++ tailWord_383022) baseStart_383022 baseEnd_383022 := by
    simpa [prefixWord, tailWord_383022, baseEnd_383022] using wordTrace_append hprefix tailTrace_383022
  have hstable : (prefixWord ++ tailWord_383022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383022).length < 2 ^ (prefixWord ++ tailWord_383022).sum := by decide
  have hdescent : baseEnd_383022 < baseStart_383022 := by decide
  rcases family_descends (prefixWord ++ tailWord_383022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383024 : List Nat := [2, 1, 1, 1, 2, 7, 5]
def baseStart_383024 : Nat := 118140960795 + 383024 * 2 ^ 59
def prefixEnd_383024 : Nat := 4983230072969 + 3 ^ 40 * 383024 * 2
def baseEnd_383024 : Nat := 38849464534876968007607

theorem tailTrace_383024 : CollatzResearch.WordTrace tailWord_383024 prefixEnd_383024 38849464534876968007607 := by
  unfold tailWord_383024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6985016482188469068166063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9313355309584625424221417 6985016482188469068166063)
  ·
    refine ⟨10477524723282703602249095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6985016482188469068166063 10477524723282703602249095)
    ·
      refine ⟨15716287084924055403373643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10477524723282703602249095 15716287084924055403373643)
      ·
        refine ⟨23574430627386083105060465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15716287084924055403373643 23574430627386083105060465)
        ·
          refine ⟨17680822970539562328795349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23574430627386083105060465 17680822970539562328795349)
          ·
            refine ⟨414394288372020992081141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17680822970539562328795349 414394288372020992081141)
            ·
              refine ⟨38849464534876968007607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414394288372020992081141 38849464534876968007607)
              ·
                rfl

theorem cell19_383024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 5].length) (baseStart_383024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383024 prefixEnd_383024 := by exact prefixLift 383024
  have htrace : WordTrace (prefixWord ++ tailWord_383024) baseStart_383024 baseEnd_383024 := by
    simpa [prefixWord, tailWord_383024, baseEnd_383024] using wordTrace_append hprefix tailTrace_383024
  have hstable : (prefixWord ++ tailWord_383024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383024).length < 2 ^ (prefixWord ++ tailWord_383024).sum := by decide
  have hdescent : baseEnd_383024 < baseStart_383024 := by decide
  rcases family_descends (prefixWord ++ tailWord_383024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383041 : List Nat := [1, 2, 5, 1, 2, 2, 2, 4]
def baseStart_383041 : Nat := 118140960795 + 383041 * 2 ^ 59
def prefixEnd_383041 : Nat := 4983230072969 + 3 ^ 40 * 383041 * 2
def baseEnd_383041 : Nat := 116553566446779901644997

theorem tailTrace_383041 : CollatzResearch.WordTrace tailWord_383041 prefixEnd_383041 116553566446779901644997 := by
  unfold tailWord_383041
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970653005315350039700977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9313768670210233359800651 13970653005315350039700977)
  ·
    refine ⟨10477989753986512529775733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13970653005315350039700977 10477989753986512529775733)
    ·
      refine ⟨982311539436235549666475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10477989753986512529775733 982311539436235549666475)
      ·
        refine ⟨1473467309154353324499713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982311539436235549666475 1473467309154353324499713)
        ·
          refine ⟨1105100481865764993374785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473467309154353324499713 1105100481865764993374785)
          ·
            refine ⟨828825361399323745031089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1105100481865764993374785 828825361399323745031089)
            ·
              refine ⟨621619021049492808773317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828825361399323745031089 621619021049492808773317)
              ·
                refine ⟨116553566446779901644997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621619021049492808773317 116553566446779901644997)
                ·
                  rfl

theorem cell19_383041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_383041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383041 prefixEnd_383041 := by exact prefixLift 383041
  have htrace : WordTrace (prefixWord ++ tailWord_383041) baseStart_383041 baseEnd_383041 := by
    simpa [prefixWord, tailWord_383041, baseEnd_383041] using wordTrace_append hprefix tailTrace_383041
  have hstable : (prefixWord ++ tailWord_383041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383041).length < 2 ^ (prefixWord ++ tailWord_383041).sum := by decide
  have hdescent : baseEnd_383041 < baseStart_383041 := by decide
  rcases family_descends (prefixWord ++ tailWord_383041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383100 : List Nat := [2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_383100 : Nat := 118140960795 + 383100 * 2 ^ 59
def prefixEnd_383100 : Nat := 4983230072969 + 3 ^ 40 * 383100 * 2
def baseEnd_383100 : Nat := 116571519251885246333725

theorem tailTrace_383100 : CollatzResearch.WordTrace tailWord_383100 prefixEnd_383100 116571519251885246333725 := by
  unfold tailWord_383100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986402456050801558049377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9315203274734402077399169 6986402456050801558049377)
  ·
    refine ⟨5239801842038101168537033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6986402456050801558049377 5239801842038101168537033)
    ·
      refine ⟨3929851381528575876402775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5239801842038101168537033 3929851381528575876402775)
      ·
        refine ⟨5894777072292863814604163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929851381528575876402775 5894777072292863814604163)
        ·
          refine ⟨8842165608439295721906245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894777072292863814604163 8842165608439295721906245)
          ·
            refine ⟨1657906051582367947857421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8842165608439295721906245 1657906051582367947857421)
            ·
              refine ⟨621714769343387980446533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1657906051582367947857421 621714769343387980446533)
              ·
                refine ⟨116571519251885246333725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621714769343387980446533 116571519251885246333725)
                ·
                  rfl

theorem cell19_383100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_383100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383100 prefixEnd_383100 := by exact prefixLift 383100
  have htrace : WordTrace (prefixWord ++ tailWord_383100) baseStart_383100 baseEnd_383100 := by
    simpa [prefixWord, tailWord_383100, baseEnd_383100] using wordTrace_append hprefix tailTrace_383100
  have hstable : (prefixWord ++ tailWord_383100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383100).length < 2 ^ (prefixWord ++ tailWord_383100).sum := by decide
  have hdescent : baseEnd_383100 < baseStart_383100 := by decide
  rcases family_descends (prefixWord ++ tailWord_383100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383170 : List Nat := [3, 5, 1, 1, 1, 1, 4, 3]
def baseStart_383170 : Nat := 118140960795 + 383170 * 2 ^ 59
def prefixEnd_383170 : Nat := 4983230072969 + 3 ^ 40 * 383170 * 2
def baseEnd_383170 : Nat := 116592819190145824777979

theorem tailTrace_383170 : CollatzResearch.WordTrace tailWord_383170 prefixEnd_383170 116592819190145824777979 := by
  unfold tailWord_383170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493839505462001267786741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9316905347898670047431309 3493839505462001267786741)
  ·
    refine ⟨327547453637062618855007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3493839505462001267786741 327547453637062618855007)
    ·
      refine ⟨491321180455593928282511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327547453637062618855007 491321180455593928282511)
      ·
        refine ⟨736981770683390892423767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491321180455593928282511 736981770683390892423767)
        ·
          refine ⟨1105472656025086338635651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736981770683390892423767 1105472656025086338635651)
          ·
            refine ⟨1658208984037629507953477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105472656025086338635651 1658208984037629507953477)
            ·
              refine ⟨310914184507055532741277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1658208984037629507953477 310914184507055532741277)
              ·
                refine ⟨116592819190145824777979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310914184507055532741277 116592819190145824777979)
                ·
                  rfl

theorem cell19_383170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_383170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383170 prefixEnd_383170 := by exact prefixLift 383170
  have htrace : WordTrace (prefixWord ++ tailWord_383170) baseStart_383170 baseEnd_383170 := by
    simpa [prefixWord, tailWord_383170, baseEnd_383170] using wordTrace_append hprefix tailTrace_383170
  have hstable : (prefixWord ++ tailWord_383170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383170).length < 2 ^ (prefixWord ++ tailWord_383170).sum := by decide
  have hdescent : baseEnd_383170 < baseStart_383170 := by decide
  rcases family_descends (prefixWord ++ tailWord_383170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383172 : List Nat := [2, 3, 3, 1, 2, 3, 2, 3]
def baseStart_383172 : Nat := 118140960795 + 383172 * 2 ^ 59
def prefixEnd_383172 : Nat := 4983230072969 + 3 ^ 40 * 383172 * 2
def baseEnd_383172 : Nat := 116593427759810412733529

theorem tailTrace_383172 : CollatzResearch.WordTrace tailWord_383172 prefixEnd_383172 116593427759810412733529 := by
  unfold tailWord_383172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987715483920379706359885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9316953978560506275146513 6987715483920379706359885)
  ·
    refine ⟨2620393306470142389884957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6987715483920379706359885 2620393306470142389884957)
    ·
      refine ⟨982647489926303396206859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2620393306470142389884957 982647489926303396206859)
      ·
        refine ⟨1473971234889455094310289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982647489926303396206859 1473971234889455094310289)
        ·
          refine ⟨1105478426167091320732717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473971234889455094310289 1105478426167091320732717)
          ·
            refine ⟨414554409812659245274769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1105478426167091320732717 414554409812659245274769)
            ·
              refine ⟨310915807359494433956077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414554409812659245274769 310915807359494433956077)
              ·
                refine ⟨116593427759810412733529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310915807359494433956077 116593427759810412733529)
                ·
                  rfl

theorem cell19_383172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_383172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383172 prefixEnd_383172 := by exact prefixLift 383172
  have htrace : WordTrace (prefixWord ++ tailWord_383172) baseStart_383172 baseEnd_383172 := by
    simpa [prefixWord, tailWord_383172, baseEnd_383172] using wordTrace_append hprefix tailTrace_383172
  have hstable : (prefixWord ++ tailWord_383172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383172).length < 2 ^ (prefixWord ++ tailWord_383172).sum := by decide
  have hdescent : baseEnd_383172 < baseStart_383172 := by decide
  rcases family_descends (prefixWord ++ tailWord_383172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383235 : List Nat := [1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_383235 : Nat := 118140960795 + 383235 * 2 ^ 59
def prefixEnd_383235 : Nat := 4983230072969 + 3 ^ 40 * 383235 * 2
def baseEnd_383235 : Nat := 116612597704244933333357

theorem tailTrace_383235 : CollatzResearch.WordTrace tailWord_383235 prefixEnd_383235 116612597704244933333357 := by
  unfold tailWord_383235
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977728766612521172263159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9318485844408347448175439 13977728766612521172263159)
  ·
    refine ⟨20966593149918781758394739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13977728766612521172263159 20966593149918781758394739)
    ·
      refine ⟨31449889724878172637592109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20966593149918781758394739 31449889724878172637592109)
      ·
        refine ⟨11793708646829314739097041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31449889724878172637592109 11793708646829314739097041)
        ·
          refine ⟨8845281485121986054322781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11793708646829314739097041 8845281485121986054322781)
          ·
            refine ⟨3316980556920744770371043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8845281485121986054322781 3316980556920744770371043)
            ·
              refine ⟨4975470835381117155556565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316980556920744770371043 4975470835381117155556565)
              ·
                refine ⟨116612597704244933333357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4975470835381117155556565 116612597704244933333357)
                ·
                  rfl

theorem cell19_383235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_383235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383235 prefixEnd_383235 := by exact prefixLift 383235
  have htrace : WordTrace (prefixWord ++ tailWord_383235) baseStart_383235 baseEnd_383235 := by
    simpa [prefixWord, tailWord_383235, baseEnd_383235] using wordTrace_append hprefix tailTrace_383235
  have hstable : (prefixWord ++ tailWord_383235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383235).length < 2 ^ (prefixWord ++ tailWord_383235).sum := by decide
  have hdescent : baseEnd_383235 < baseStart_383235 := by decide
  rcases family_descends (prefixWord ++ tailWord_383235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383269 : List Nat := [1, 3, 1, 2, 5, 2, 1, 4]
def baseStart_383269 : Nat := 118140960795 + 383269 * 2 ^ 59
def prefixEnd_383269 : Nat := 4983230072969 + 3 ^ 40 * 383269 * 2
def baseEnd_383269 : Nat := 116622943388542928577709

theorem tailTrace_383269 : CollatzResearch.WordTrace tailWord_383269 prefixEnd_383269 116622943388542928577709 := by
  unfold tailWord_383269
  simp only [CollatzResearch.WordTrace]
  refine ⟨13978968848489344979000861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9319312565659563319333907 13978968848489344979000861)
  ·
    refine ⟨5242113318183504367125323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13978968848489344979000861 5242113318183504367125323)
    ·
      refine ⟨7863169977275256550687985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5242113318183504367125323 7863169977275256550687985)
      ·
        refine ⟨5897377482956442413015989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7863169977275256550687985 5897377482956442413015989)
        ·
          refine ⟨552879139027166476220249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5897377482956442413015989 552879139027166476220249)
          ·
            refine ⟨414659354270374857165187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552879139027166476220249 414659354270374857165187)
            ·
              refine ⟨621989031405562285747781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414659354270374857165187 621989031405562285747781)
              ·
                refine ⟨116622943388542928577709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 621989031405562285747781 116622943388542928577709)
                ·
                  rfl

theorem cell19_383269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_383269 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383269 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383269 prefixEnd_383269 := by exact prefixLift 383269
  have htrace : WordTrace (prefixWord ++ tailWord_383269) baseStart_383269 baseEnd_383269 := by
    simpa [prefixWord, tailWord_383269, baseEnd_383269] using wordTrace_append hprefix tailTrace_383269
  have hstable : (prefixWord ++ tailWord_383269).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383269).length < 2 ^ (prefixWord ++ tailWord_383269).sum := by decide
  have hdescent : baseEnd_383269 < baseStart_383269 := by decide
  rcases family_descends (prefixWord ++ tailWord_383269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383362 : List Nat := [3, 4, 2, 1, 2, 2, 5]
def baseStart_383362 : Nat := 118140960795 + 383362 * 2 ^ 59
def prefixEnd_383362 : Nat := 4983230072969 + 3 ^ 40 * 383362 * 2
def baseEnd_383362 : Nat := 38883747292648756170263

theorem tailTrace_383362 : CollatzResearch.WordTrace tailWord_383362 prefixEnd_383362 38883747292648756170263 := by
  unfold tailWord_383362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495590209288105465534085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9321573891434947908090893 3495590209288105465534085)
  ·
    refine ⟨655423164241519774787641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3495590209288105465534085 655423164241519774787641)
    ·
      refine ⟨491567373181139831090731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 655423164241519774787641 491567373181139831090731)
      ·
        refine ⟨737351059771709746636097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491567373181139831090731 737351059771709746636097)
        ·
          refine ⟨553013294828782309977073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 737351059771709746636097 553013294828782309977073)
          ·
            refine ⟨414759971121586732482805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553013294828782309977073 414759971121586732482805)
            ·
              refine ⟨38883747292648756170263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 414759971121586732482805 38883747292648756170263)
              ·
                rfl

theorem cell19_383362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_383362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383362 prefixEnd_383362 := by exact prefixLift 383362
  have htrace : WordTrace (prefixWord ++ tailWord_383362) baseStart_383362 baseEnd_383362 := by
    simpa [prefixWord, tailWord_383362, baseEnd_383362] using wordTrace_append hprefix tailTrace_383362
  have hstable : (prefixWord ++ tailWord_383362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383362).length < 2 ^ (prefixWord ++ tailWord_383362).sum := by decide
  have hdescent : baseEnd_383362 < baseStart_383362 := by decide
  rcases family_descends (prefixWord ++ tailWord_383362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383459 : List Nat := [1, 1, 1, 6, 3, 1, 3, 3]
def baseStart_383459 : Nat := 118140960795 + 383459 * 2 ^ 59
def prefixEnd_383459 : Nat := 4983230072969 + 3 ^ 40 * 383459 * 2
def baseEnd_383459 : Nat := 116680757506678784354969

theorem tailTrace_383459 : CollatzResearch.WordTrace tailWord_383459 prefixEnd_383459 116680757506678784354969 := by
  unfold tailWord_383459
  simp only [CollatzResearch.WordTrace]
  refine ⟨13985898717801007428417431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9323932478534004952278287 13985898717801007428417431)
  ·
    refine ⟨20978848076701511142626147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13985898717801007428417431 20978848076701511142626147)
    ·
      refine ⟨31468272115052266713939221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20978848076701511142626147 31468272115052266713939221)
      ·
        refine ⟨1475075255393075002215901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31468272115052266713939221 1475075255393075002215901)
        ·
          refine ⟨553153220772403125830963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1475075255393075002215901 553153220772403125830963)
          ·
            refine ⟨829729831158604688746445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553153220772403125830963 829729831158604688746445)
            ·
              refine ⟨311148686684476758279917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829729831158604688746445 311148686684476758279917)
              ·
                refine ⟨116680757506678784354969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311148686684476758279917 116680757506678784354969)
                ·
                  rfl

theorem cell19_383459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_383459 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383459 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383459 prefixEnd_383459 := by exact prefixLift 383459
  have htrace : WordTrace (prefixWord ++ tailWord_383459) baseStart_383459 baseEnd_383459 := by
    simpa [prefixWord, tailWord_383459, baseEnd_383459] using wordTrace_append hprefix tailTrace_383459
  have hstable : (prefixWord ++ tailWord_383459).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383459).length < 2 ^ (prefixWord ++ tailWord_383459).sum := by decide
  have hdescent : baseEnd_383459 < baseStart_383459 := by decide
  rcases family_descends (prefixWord ++ tailWord_383459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383516 : List Nat := [2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_383516 : Nat := 118140960795 + 383516 * 2 ^ 59
def prefixEnd_383516 : Nat := 4983230072969 + 3 ^ 40 * 383516 * 2
def baseEnd_383516 : Nat := 116698101742119541088147

theorem tailTrace_383516 : CollatzResearch.WordTrace tailWord_383516 prefixEnd_383516 116698101742119541088147 := by
  unfold tailWord_383516
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993988839297253081621201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9325318452396337442161601 6993988839297253081621201)
  ·
    refine ⟨5245491629472939811215901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6993988839297253081621201 5245491629472939811215901)
    ·
      refine ⟨1967059361052352429205963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5245491629472939811215901 1967059361052352429205963)
      ·
        refine ⟨2950589041578528643808945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967059361052352429205963 2950589041578528643808945)
        ·
          refine ⟨2212941781183896482856709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2950589041578528643808945 2212941781183896482856709)
          ·
            refine ⟨414926583971980590535633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2212941781183896482856709 414926583971980590535633)
            ·
              refine ⟨311194937978985442901725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414926583971980590535633 311194937978985442901725)
              ·
                refine ⟨116698101742119541088147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311194937978985442901725 116698101742119541088147)
                ·
                  rfl

theorem cell19_383516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_383516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383516 prefixEnd_383516 := by exact prefixLift 383516
  have htrace : WordTrace (prefixWord ++ tailWord_383516) baseStart_383516 baseEnd_383516 := by
    simpa [prefixWord, tailWord_383516, baseEnd_383516] using wordTrace_append hprefix tailTrace_383516
  have hstable : (prefixWord ++ tailWord_383516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383516).length < 2 ^ (prefixWord ++ tailWord_383516).sum := by decide
  have hdescent : baseEnd_383516 < baseStart_383516 := by decide
  rcases family_descends (prefixWord ++ tailWord_383516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383708 : List Nat := [2, 2, 5, 1, 1, 1, 7]
def baseStart_383708 : Nat := 118140960795 + 383708 * 2 ^ 59
def prefixEnd_383708 : Nat := 4983230072969 + 3 ^ 40 * 383708 * 2
def baseEnd_383708 : Nat := 38918841476639994940319

theorem tailTrace_383708 : CollatzResearch.WordTrace tailWord_383708 prefixEnd_383708 38918841476639994940319 := by
  unfold tailWord_383708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6997490246949461477115889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9329986995932615302821185 6997490246949461477115889)
  ·
    refine ⟨5248117685212096107836917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6997490246949461477115889 5248117685212096107836917)
    ·
      refine ⟨492011032988634010109711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5248117685212096107836917 492011032988634010109711)
      ·
        refine ⟨738016549482951015164567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492011032988634010109711 738016549482951015164567)
        ·
          refine ⟨1107024824224426522746851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738016549482951015164567 1107024824224426522746851)
          ·
            refine ⟨1660537236336639784120277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107024824224426522746851 1660537236336639784120277)
            ·
              refine ⟨38918841476639994940319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1660537236336639784120277 38918841476639994940319)
              ·
                rfl

theorem cell19_383708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_383708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383708 prefixEnd_383708 := by exact prefixLift 383708
  have htrace : WordTrace (prefixWord ++ tailWord_383708) baseStart_383708 baseEnd_383708 := by
    simpa [prefixWord, tailWord_383708, baseEnd_383708] using wordTrace_append hprefix tailTrace_383708
  have hstable : (prefixWord ++ tailWord_383708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383708).length < 2 ^ (prefixWord ++ tailWord_383708).sum := by decide
  have hdescent : baseEnd_383708 < baseStart_383708 := by decide
  rcases family_descends (prefixWord ++ tailWord_383708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383729 : List Nat := [1, 2, 2, 2, 2, 2, 4, 4]
def baseStart_383729 : Nat := 118140960795 + 383729 * 2 ^ 59
def prefixEnd_383729 : Nat := 4983230072969 + 3 ^ 40 * 383729 * 2
def baseEnd_383729 : Nat := 116762914411398158354233

theorem tailTrace_383729 : CollatzResearch.WordTrace tailWord_383729 prefixEnd_383729 116762914411398158354233 := by
  unfold tailWord_383729
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995746426822843540746241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9330497617881895693830827 13995746426822843540746241)
  ·
    refine ⟨10496809820117132655559681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13995746426822843540746241 10496809820117132655559681)
    ·
      refine ⟨7872607365087849491669761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10496809820117132655559681 7872607365087849491669761)
      ·
        refine ⟨5904455523815887118752321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7872607365087849491669761 5904455523815887118752321)
        ·
          refine ⟨4428341642861915339064241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5904455523815887118752321 4428341642861915339064241)
          ·
            refine ⟨3321256232146436504298181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4428341642861915339064241 3321256232146436504298181)
            ·
              refine ⟨622735543527456844555909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3321256232146436504298181 622735543527456844555909)
              ·
                refine ⟨116762914411398158354233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622735543527456844555909 116762914411398158354233)
                ·
                  rfl

theorem cell19_383729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_383729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383729 prefixEnd_383729 := by exact prefixLift 383729
  have htrace : WordTrace (prefixWord ++ tailWord_383729) baseStart_383729 baseEnd_383729 := by
    simpa [prefixWord, tailWord_383729, baseEnd_383729] using wordTrace_append hprefix tailTrace_383729
  have hstable : (prefixWord ++ tailWord_383729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383729).length < 2 ^ (prefixWord ++ tailWord_383729).sum := by decide
  have hdescent : baseEnd_383729 < baseStart_383729 := by decide
  rcases family_descends (prefixWord ++ tailWord_383729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383746 : List Nat := [3, 4, 1, 1, 1, 2, 2, 5]
def baseStart_383746 : Nat := 118140960795 + 383746 * 2 ^ 59
def prefixEnd_383746 : Nat := 4983230072969 + 3 ^ 40 * 383746 * 2
def baseEnd_383746 : Nat := 116768087253547155976409

theorem tailTrace_383746 : CollatzResearch.WordTrace tailWord_383746 prefixEnd_383746 116768087253547155976409 := by
  unfold tailWord_383746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499091616940313861028773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9330910978507503629410061 3499091616940313861028773)
  ·
    refine ⟨656079678176308848942895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3499091616940313861028773 656079678176308848942895)
    ·
      refine ⟨984119517264463273414343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 656079678176308848942895 984119517264463273414343)
      ·
        refine ⟨1476179275896694910121515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984119517264463273414343 1476179275896694910121515)
        ·
          refine ⟨2214268913845042365182273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476179275896694910121515 2214268913845042365182273)
          ·
            refine ⟨1660701685383781773886705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2214268913845042365182273 1660701685383781773886705)
            ·
              refine ⟨1245526264037836330415029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660701685383781773886705 1245526264037836330415029)
              ·
                refine ⟨116768087253547155976409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1245526264037836330415029 116768087253547155976409)
                ·
                  rfl

theorem cell19_383746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_383746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383746 prefixEnd_383746 := by exact prefixLift 383746
  have htrace : WordTrace (prefixWord ++ tailWord_383746) baseStart_383746 baseEnd_383746 := by
    simpa [prefixWord, tailWord_383746, baseEnd_383746] using wordTrace_append hprefix tailTrace_383746
  have hstable : (prefixWord ++ tailWord_383746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383746).length < 2 ^ (prefixWord ++ tailWord_383746).sum := by decide
  have hdescent : baseEnd_383746 < baseStart_383746 := by decide
  rcases family_descends (prefixWord ++ tailWord_383746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383748 : List Nat := [2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_383748 : Nat := 118140960795 + 383748 * 2 ^ 59
def prefixEnd_383748 : Nat := 4983230072969 + 3 ^ 40 * 383748 * 2
def baseEnd_383748 : Nat := 116768695823211743931959

theorem tailTrace_383748 : CollatzResearch.WordTrace tailWord_383748 prefixEnd_383748 116768695823211743931959 := by
  unfold tailWord_383748
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998219706877004892843949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9330959609169339857125265 6998219706877004892843949)
  ·
    refine ⟨2624332390078876834816481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6998219706877004892843949 2624332390078876834816481)
    ·
      refine ⟨1968249292559157626112361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2624332390078876834816481 1968249292559157626112361)
      ·
        refine ⟨1476186969419368219584271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1968249292559157626112361 1476186969419368219584271)
        ·
          refine ⟨2214280454129052329376407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476186969419368219584271 2214280454129052329376407)
          ·
            refine ⟨3321420681193578494064611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214280454129052329376407 3321420681193578494064611)
            ·
              refine ⟨4982131021790367741096917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321420681193578494064611 4982131021790367741096917)
              ·
                refine ⟨116768695823211743931959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4982131021790367741096917 116768695823211743931959)
                ·
                  rfl

theorem cell19_383748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_383748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383748 prefixEnd_383748 := by exact prefixLift 383748
  have htrace : WordTrace (prefixWord ++ tailWord_383748) baseStart_383748 baseEnd_383748 := by
    simpa [prefixWord, tailWord_383748, baseEnd_383748] using wordTrace_append hprefix tailTrace_383748
  have hstable : (prefixWord ++ tailWord_383748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383748).length < 2 ^ (prefixWord ++ tailWord_383748).sum := by decide
  have hdescent : baseEnd_383748 < baseStart_383748 := by decide
  rcases family_descends (prefixWord ++ tailWord_383748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383767 : List Nat := [1, 1, 3, 4, 3, 7]
def baseStart_383767 : Nat := 118140960795 + 383767 * 2 ^ 59
def prefixEnd_383767 : Nat := 4983230072969 + 3 ^ 40 * 383767 * 2
def baseEnd_383767 : Nat := 12974941915002814389965

theorem tailTrace_383767 : CollatzResearch.WordTrace tailWord_383767 prefixEnd_383767 12974941915002814389965 := by
  unfold tailWord_383767
  simp only [CollatzResearch.WordTrace]
  refine ⟨13997132400685176030629555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9331421600456784020419703 13997132400685176030629555)
  ·
    refine ⟨20995698601027764045944333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13997132400685176030629555 20995698601027764045944333)
    ·
      refine ⟨7873386975385411517229125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20995698601027764045944333 7873386975385411517229125)
      ·
        refine ⟨1476260057884764659480461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7873386975385411517229125 1476260057884764659480461)
        ·
          refine ⟨553597521706786747305173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1476260057884764659480461 553597521706786747305173)
          ·
            refine ⟨12974941915002814389965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 553597521706786747305173 12974941915002814389965)
            ·
              rfl

theorem cell19_383767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 7].length) (baseStart_383767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383767 prefixEnd_383767 := by exact prefixLift 383767
  have htrace : WordTrace (prefixWord ++ tailWord_383767) baseStart_383767 baseEnd_383767 := by
    simpa [prefixWord, tailWord_383767, baseEnd_383767] using wordTrace_append hprefix tailTrace_383767
  have hstable : (prefixWord ++ tailWord_383767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383767).length < 2 ^ (prefixWord ++ tailWord_383767).sum := by decide
  have hdescent : baseEnd_383767 < baseStart_383767 := by decide
  rcases family_descends (prefixWord ++ tailWord_383767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383881 : List Nat := [1, 2, 1, 1, 5, 4, 5]
def baseStart_383881 : Nat := 118140960795 + 383881 * 2 ^ 59
def prefixEnd_383881 : Nat := 4983230072969 + 3 ^ 40 * 383881 * 2
def baseEnd_383881 : Nat := 38936388568635614325347

theorem tailTrace_383881 : CollatzResearch.WordTrace tailWord_383881 prefixEnd_383881 38936388568635614325347 := by
  unfold tailWord_383881
  simp only [CollatzResearch.WordTrace]
  refine ⟨14001290322272173500279497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9334193548181449000186331 14001290322272173500279497)
  ·
    refine ⟨10500967741704130125209623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14001290322272173500279497 10500967741704130125209623)
    ·
      refine ⟨15751451612556195187814435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500967741704130125209623 15751451612556195187814435)
      ·
        refine ⟨23627177418834292781721653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15751451612556195187814435 23627177418834292781721653)
        ·
          refine ⟨2215047883015714948286405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23627177418834292781721653 2215047883015714948286405)
          ·
            refine ⟨415321478065446552803701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2215047883015714948286405 415321478065446552803701)
            ·
              refine ⟨38936388568635614325347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 415321478065446552803701 38936388568635614325347)
              ·
                rfl

theorem cell19_383881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_383881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383881 prefixEnd_383881 := by exact prefixLift 383881
  have htrace : WordTrace (prefixWord ++ tailWord_383881) baseStart_383881 baseEnd_383881 := by
    simpa [prefixWord, tailWord_383881, baseEnd_383881] using wordTrace_append hprefix tailTrace_383881
  have hstable : (prefixWord ++ tailWord_383881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383881).length < 2 ^ (prefixWord ++ tailWord_383881).sum := by decide
  have hdescent : baseEnd_383881 < baseStart_383881 := by decide
  rcases family_descends (prefixWord ++ tailWord_383881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383883 : List Nat := [1, 1, 1, 1, 4, 2, 9]
def baseStart_383883 : Nat := 118140960795 + 383883 * 2 ^ 59
def prefixEnd_383883 : Nat := 4983230072969 + 3 ^ 40 * 383883 * 2
def baseEnd_383883 : Nat := 38936591425190476977197

theorem tailTrace_383883 : CollatzResearch.WordTrace tailWord_383883 prefixEnd_383883 38936591425190476977197 := by
  unfold tailWord_383883
  simp only [CollatzResearch.WordTrace]
  refine ⟨14001363268264927841852303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9334242178843285227901535 14001363268264927841852303)
  ·
    refine ⟨21002044902397391762778455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14001363268264927841852303 21002044902397391762778455)
    ·
      refine ⟨31503067353596087644167683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21002044902397391762778455 31503067353596087644167683)
      ·
        refine ⟨47254601030394131466251525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31503067353596087644167683 47254601030394131466251525)
        ·
          refine ⟨8860237693198899649922161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47254601030394131466251525 8860237693198899649922161)
          ·
            refine ⟨6645178269899174737441621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8860237693198899649922161 6645178269899174737441621)
            ·
              refine ⟨38936591425190476977197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6645178269899174737441621 38936591425190476977197)
              ·
                rfl

theorem cell19_383883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_383883 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383883 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383883 prefixEnd_383883 := by exact prefixLift 383883
  have htrace : WordTrace (prefixWord ++ tailWord_383883) baseStart_383883 baseEnd_383883 := by
    simpa [prefixWord, tailWord_383883, baseEnd_383883] using wordTrace_append hprefix tailTrace_383883
  have hstable : (prefixWord ++ tailWord_383883).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383883).length < 2 ^ (prefixWord ++ tailWord_383883).sum := by decide
  have hdescent : baseEnd_383883 < baseStart_383883 := by decide
  rcases family_descends (prefixWord ++ tailWord_383883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383894 : List Nat := [5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_383894 : Nat := 118140960795 + 383894 * 2 ^ 59
def prefixEnd_383894 : Nat := 4983230072969 + 3 ^ 40 * 383894 * 2
def baseEnd_383894 : Nat := 116813121408726664687117

theorem tailTrace_383894 : CollatzResearch.WordTrace tailWord_383894 prefixEnd_383894 116813121408726664687117 := by
  unfold tailWord_383894
  simp only [CollatzResearch.WordTrace]
  refine ⟨875110279451567295031421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9334509647483384480335157 875110279451567295031421)
  ·
    refine ⟨328166354794337735636783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 875110279451567295031421 328166354794337735636783)
    ·
      refine ⟨492249532191506603455175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 328166354794337735636783 492249532191506603455175)
      ·
        refine ⟨738374298287259905182763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 492249532191506603455175 738374298287259905182763)
        ·
          refine ⟨1107561447430889857774145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738374298287259905182763 1107561447430889857774145)
          ·
            refine ⟨830671085573167393330609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107561447430889857774145 830671085573167393330609)
            ·
              refine ⟨623003314179875544997957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830671085573167393330609 623003314179875544997957)
              ·
                refine ⟨116813121408726664687117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623003314179875544997957 116813121408726664687117)
                ·
                  rfl

theorem cell19_383894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_383894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383894 prefixEnd_383894 := by exact prefixLift 383894
  have htrace : WordTrace (prefixWord ++ tailWord_383894) baseStart_383894 baseEnd_383894 := by
    simpa [prefixWord, tailWord_383894, baseEnd_383894] using wordTrace_append hprefix tailTrace_383894
  have hstable : (prefixWord ++ tailWord_383894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383894).length < 2 ^ (prefixWord ++ tailWord_383894).sum := by decide
  have hdescent : baseEnd_383894 < baseStart_383894 := by decide
  rcases family_descends (prefixWord ++ tailWord_383894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383898 : List Nat := [3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_383898 : Nat := 118140960795 + 383898 * 2 ^ 59
def prefixEnd_383898 : Nat := 4983230072969 + 3 ^ 40 * 383898 * 2
def baseEnd_383898 : Nat := 116814338548055840598217

theorem tailTrace_383898 : CollatzResearch.WordTrace tailWord_383898 prefixEnd_383898 116814338548055840598217 := by
  unfold tailWord_383898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500477590802646350912087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9334606908807056935765565 3500477590802646350912087)
  ·
    refine ⟨5250716386203969526368131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3500477590802646350912087 5250716386203969526368131)
    ·
      refine ⟨7876074579305954289552197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5250716386203969526368131 7876074579305954289552197)
      ·
        refine ⟨1476763983619866429291037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7876074579305954289552197 1476763983619866429291037)
        ·
          refine ⟨553786493857449910984139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1476763983619866429291037 553786493857449910984139)
          ·
            refine ⟨830679740786174866476209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553786493857449910984139 830679740786174866476209)
            ·
              refine ⟨623009805589631149857157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830679740786174866476209 623009805589631149857157)
              ·
                refine ⟨116814338548055840598217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623009805589631149857157 116814338548055840598217)
                ·
                  rfl

theorem cell19_383898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_383898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383898 prefixEnd_383898 := by exact prefixLift 383898
  have htrace : WordTrace (prefixWord ++ tailWord_383898) baseStart_383898 baseEnd_383898 := by
    simpa [prefixWord, tailWord_383898, baseEnd_383898] using wordTrace_append hprefix tailTrace_383898
  have hstable : (prefixWord ++ tailWord_383898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383898).length < 2 ^ (prefixWord ++ tailWord_383898).sum := by decide
  have hdescent : baseEnd_383898 < baseStart_383898 := by decide
  rcases family_descends (prefixWord ++ tailWord_383898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383938 : List Nat := [3, 5, 11]
def baseStart_383938 : Nat := 118140960795 + 383938 * 2 ^ 59
def prefixEnd_383938 : Nat := 4983230072969 + 3 ^ 40 * 383938 * 2
def baseEnd_383938 : Nat := 480767530622829628433

theorem tailTrace_383938 : CollatzResearch.WordTrace tailWord_383938 prefixEnd_383938 480767530622829628433 := by
  unfold tailWord_383938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500842320766418058776117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9335579522043781490069645 3500842320766418058776117)
  ·
    refine ⟨328203967571851693010261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3500842320766418058776117 328203967571851693010261)
    ·
      refine ⟨480767530622829628433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 11 328203967571851693010261 480767530622829628433)
      ·
        rfl

theorem cell19_383938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 11].length) (baseStart_383938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383938 prefixEnd_383938 := by exact prefixLift 383938
  have htrace : WordTrace (prefixWord ++ tailWord_383938) baseStart_383938 baseEnd_383938 := by
    simpa [prefixWord, tailWord_383938, baseEnd_383938] using wordTrace_append hprefix tailTrace_383938
  have hstable : (prefixWord ++ tailWord_383938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383938).length < 2 ^ (prefixWord ++ tailWord_383938).sum := by decide
  have hdescent : baseEnd_383938 < baseStart_383938 := by decide
  rcases family_descends (prefixWord ++ tailWord_383938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383949 : List Nat := [1, 6, 3, 1, 1, 2, 1, 4]
def baseStart_383949 : Nat := 118140960795 + 383949 * 2 ^ 59
def prefixEnd_383949 : Nat := 4983230072969 + 3 ^ 40 * 383949 * 2
def baseEnd_383949 : Nat := 116829857074502833464745

theorem tailTrace_383949 : CollatzResearch.WordTrace tailWord_383949 prefixEnd_383949 116829857074502833464745 := by
  unfold tailWord_383949
  simp only [CollatzResearch.WordTrace]
  refine ⟨14003770486025821113754901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9335846990683880742503267 14003770486025821113754901)
  ·
    refine ⟨656426741532460364707261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14003770486025821113754901 656426741532460364707261)
    ·
      refine ⟨246160028074672636765223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 656426741532460364707261 246160028074672636765223)
      ·
        refine ⟨369240042112008955147835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246160028074672636765223 369240042112008955147835)
        ·
          refine ⟨553860063168013432721753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369240042112008955147835 553860063168013432721753)
          ·
            refine ⟨415395047376010074541315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553860063168013432721753 415395047376010074541315)
            ·
              refine ⟨623092571064015111811973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415395047376010074541315 623092571064015111811973)
              ·
                refine ⟨116829857074502833464745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623092571064015111811973 116829857074502833464745)
                ·
                  rfl

theorem cell19_383949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_383949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383949 prefixEnd_383949 := by exact prefixLift 383949
  have htrace : WordTrace (prefixWord ++ tailWord_383949) baseStart_383949 baseEnd_383949 := by
    simpa [prefixWord, tailWord_383949, baseEnd_383949] using wordTrace_append hprefix tailTrace_383949
  have hstable : (prefixWord ++ tailWord_383949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383949).length < 2 ^ (prefixWord ++ tailWord_383949).sum := by decide
  have hdescent : baseEnd_383949 < baseStart_383949 := by decide
  rcases family_descends (prefixWord ++ tailWord_383949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383959 : List Nat := [1, 1, 3, 2, 1, 1, 2, 8]
def baseStart_383959 : Nat := 118140960795 + 383959 * 2 ^ 59
def prefixEnd_383959 : Nat := 4983230072969 + 3 ^ 40 * 383959 * 2
def baseEnd_383959 : Nat := 116832899922825773242495

theorem tailTrace_383959 : CollatzResearch.WordTrace tailWord_383959 prefixEnd_383959 116832899922825773242495 := by
  unfold tailWord_383959
  simp only [CollatzResearch.WordTrace]
  refine ⟨14004135215989592821618931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9336090143993061881079287 14004135215989592821618931)
  ·
    refine ⟨21006202823984389232428397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14004135215989592821618931 21006202823984389232428397)
    ·
      refine ⟨7877326058994145962160649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21006202823984389232428397 7877326058994145962160649)
      ·
        refine ⟨5907994544245609471620487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7877326058994145962160649 5907994544245609471620487)
        ·
          refine ⟨8861991816368414207430731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5907994544245609471620487 8861991816368414207430731)
          ·
            refine ⟨13292987724552621311146097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861991816368414207430731 13292987724552621311146097)
            ·
              refine ⟨9969740793414465983359573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13292987724552621311146097 9969740793414465983359573)
              ·
                refine ⟨116832899922825773242495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9969740793414465983359573 116832899922825773242495)
                ·
                  rfl

theorem cell19_383959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_383959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_383959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_383959 prefixEnd_383959 := by exact prefixLift 383959
  have htrace : WordTrace (prefixWord ++ tailWord_383959) baseStart_383959 baseEnd_383959 := by
    simpa [prefixWord, tailWord_383959, baseEnd_383959] using wordTrace_append hprefix tailTrace_383959
  have hstable : (prefixWord ++ tailWord_383959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383959).length < 2 ^ (prefixWord ++ tailWord_383959).sum := by decide
  have hdescent : baseEnd_383959 < baseStart_383959 := by decide
  rcases family_descends (prefixWord ++ tailWord_383959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384029 : List Nat := [1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_384029 : Nat := 118140960795 + 384029 * 2 ^ 59
def prefixEnd_384029 : Nat := 4983230072969 + 3 ^ 40 * 384029 * 2
def baseEnd_384029 : Nat := 116854199861086351686749

theorem tailTrace_384029 : CollatzResearch.WordTrace tailWord_384029 prefixEnd_384029 116854199861086351686749 := by
  unfold tailWord_384029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006688325735994776667141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9337792217157329851111427 14006688325735994776667141)
  ·
    refine ⟨2626254061075499020625089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14006688325735994776667141 2626254061075499020625089)
    ·
      refine ⟨1969690545806624265468817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2626254061075499020625089 1969690545806624265468817)
      ·
        refine ⟨1477267909354968199101613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1969690545806624265468817 1477267909354968199101613)
        ·
          refine ⟨553975466008113074663105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1477267909354968199101613 553975466008113074663105)
          ·
            refine ⟨415481599506084805997329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553975466008113074663105 415481599506084805997329)
            ·
              refine ⟨311611199629563604497997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415481599506084805997329 311611199629563604497997)
              ·
                refine ⟨116854199861086351686749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311611199629563604497997 116854199861086351686749)
                ·
                  rfl

theorem cell19_384029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_384029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384029 prefixEnd_384029 := by exact prefixLift 384029
  have htrace : WordTrace (prefixWord ++ tailWord_384029) baseStart_384029 baseEnd_384029 := by
    simpa [prefixWord, tailWord_384029, baseEnd_384029] using wordTrace_append hprefix tailTrace_384029
  have hstable : (prefixWord ++ tailWord_384029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384029).length < 2 ^ (prefixWord ++ tailWord_384029).sum := by decide
  have hdescent : baseEnd_384029 < baseStart_384029 := by decide
  rcases family_descends (prefixWord ++ tailWord_384029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384031 : List Nat := [1, 1, 2, 4, 1, 5, 2, 3]
def baseStart_384031 : Nat := 118140960795 + 384031 * 2 ^ 59
def prefixEnd_384031 : Nat := 4983230072969 + 3 ^ 40 * 384031 * 2
def baseEnd_384031 : Nat := 116854808430750939642299

theorem tailTrace_384031 : CollatzResearch.WordTrace tailWord_384031 prefixEnd_384031 116854808430750939642299 := by
  unfold tailWord_384031
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006761271728749118239947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9337840847819166078826631 14006761271728749118239947)
  ·
    refine ⟨21010141907593123677359921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14006761271728749118239947 21010141907593123677359921)
    ·
      refine ⟨15757606430694842758019941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21010141907593123677359921 15757606430694842758019941)
      ·
        refine ⟨2954551205755283017128739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15757606430694842758019941 2954551205755283017128739)
        ·
          refine ⟨4431826808632924525693109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954551205755283017128739 4431826808632924525693109)
          ·
            refine ⟨415483763309336674283729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4431826808632924525693109 415483763309336674283729)
            ·
              refine ⟨311612822482002505712797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415483763309336674283729 311612822482002505712797)
              ·
                refine ⟨116854808430750939642299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311612822482002505712797 116854808430750939642299)
                ·
                  rfl

theorem cell19_384031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_384031 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384031 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384031 prefixEnd_384031 := by exact prefixLift 384031
  have htrace : WordTrace (prefixWord ++ tailWord_384031) baseStart_384031 baseEnd_384031 := by
    simpa [prefixWord, tailWord_384031, baseEnd_384031] using wordTrace_append hprefix tailTrace_384031
  have hstable : (prefixWord ++ tailWord_384031).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384031).length < 2 ^ (prefixWord ++ tailWord_384031).sum := by decide
  have hdescent : baseEnd_384031 < baseStart_384031 := by decide
  rcases family_descends (prefixWord ++ tailWord_384031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384033 : List Nat := [1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_384033 : Nat := 118140960795 + 384033 * 2 ^ 59
def prefixEnd_384033 : Nat := 4983230072969 + 3 ^ 40 * 384033 * 2
def baseEnd_384033 : Nat := 116855417000415527597849

theorem tailTrace_384033 : CollatzResearch.WordTrace tailWord_384033 prefixEnd_384033 116855417000415527597849 := by
  unfold tailWord_384033
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006834217721503459812753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9337889478481002306541835 14006834217721503459812753)
  ·
    refine ⟨10505125663291127594859565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14006834217721503459812753 10505125663291127594859565)
    ·
      refine ⟨3939422123734172848072337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10505125663291127594859565 3939422123734172848072337)
      ·
        refine ⟨2954566592800629636054253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3939422123734172848072337 2954566592800629636054253)
        ·
          refine ⟨1107962472300236113520345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2954566592800629636054253 1107962472300236113520345)
          ·
            refine ⟨830971854225177085140259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107962472300236113520345 830971854225177085140259)
            ·
              refine ⟨1246457781337765627710389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830971854225177085140259 1246457781337765627710389)
              ·
                refine ⟨116855417000415527597849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1246457781337765627710389 116855417000415527597849)
                ·
                  rfl

theorem cell19_384033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_384033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384033 prefixEnd_384033 := by exact prefixLift 384033
  have htrace : WordTrace (prefixWord ++ tailWord_384033) baseStart_384033 baseEnd_384033 := by
    simpa [prefixWord, tailWord_384033, baseEnd_384033] using wordTrace_append hprefix tailTrace_384033
  have hstable : (prefixWord ++ tailWord_384033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384033).length < 2 ^ (prefixWord ++ tailWord_384033).sum := by decide
  have hdescent : baseEnd_384033 < baseStart_384033 := by decide
  rcases family_descends (prefixWord ++ tailWord_384033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384071 : List Nat := [1, 1, 4, 1, 3, 3, 2, 4]
def baseStart_384071 : Nat := 118140960795 + 384071 * 2 ^ 59
def prefixEnd_384071 : Nat := 4983230072969 + 3 ^ 40 * 384071 * 2
def baseEnd_384071 : Nat := 116866979824042698753301

theorem tailTrace_384071 : CollatzResearch.WordTrace tailWord_384071 prefixEnd_384071 116866979824042698753301 := by
  unfold tailWord_384071
  simp only [CollatzResearch.WordTrace]
  refine ⟨14008220191583835949696067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9338813461055890633130711 14008220191583835949696067)
  ·
    refine ⟨21012330287375753924544101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14008220191583835949696067 21012330287375753924544101)
    ·
      refine ⟨3939811928882953860852019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21012330287375753924544101 3939811928882953860852019)
      ·
        refine ⟨5909717893324430791278029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939811928882953860852019 5909717893324430791278029)
        ·
          refine ⟨2216144209996661546729261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5909717893324430791278029 2216144209996661546729261)
          ·
            refine ⟨831054078748748080023473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2216144209996661546729261 831054078748748080023473)
            ·
              refine ⟨623290559061561060017605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831054078748748080023473 623290559061561060017605)
              ·
                refine ⟨116866979824042698753301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623290559061561060017605 116866979824042698753301)
                ·
                  rfl

theorem cell19_384071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_384071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384071 prefixEnd_384071 := by exact prefixLift 384071
  have htrace : WordTrace (prefixWord ++ tailWord_384071) baseStart_384071 baseEnd_384071 := by
    simpa [prefixWord, tailWord_384071, baseEnd_384071] using wordTrace_append hprefix tailTrace_384071
  have hstable : (prefixWord ++ tailWord_384071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384071).length < 2 ^ (prefixWord ++ tailWord_384071).sum := by decide
  have hdescent : baseEnd_384071 < baseStart_384071 := by decide
  rcases family_descends (prefixWord ++ tailWord_384071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384198 : List Nat := [6, 1, 2, 2, 1, 1, 1, 5]
def baseStart_384198 : Nat := 118140960795 + 384198 * 2 ^ 59
def prefixEnd_384198 : Nat := 4983230072969 + 3 ^ 40 * 384198 * 2
def baseEnd_384198 : Nat := 116905623997744033930733

theorem tailTrace_384198 : CollatzResearch.WordTrace tailWord_384198 prefixEnd_384198 116905623997744033930733 := by
  unfold tailWord_384198
  simp only [CollatzResearch.WordTrace]
  refine ⟨437901633191366769986539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9341901508082491093046165 437901633191366769986539)
  ·
    refine ⟨656852449787050154979809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437901633191366769986539 656852449787050154979809)
    ·
      refine ⟨492639337340287616234857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 656852449787050154979809 492639337340287616234857)
      ·
        refine ⟨369479503005215712176143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 492639337340287616234857 369479503005215712176143)
        ·
          refine ⟨554219254507823568264215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369479503005215712176143 554219254507823568264215)
          ·
            refine ⟨831328881761735352396323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554219254507823568264215 831328881761735352396323)
            ·
              refine ⟨1246993322642603028594485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831328881761735352396323 1246993322642603028594485)
              ·
                refine ⟨116905623997744033930733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1246993322642603028594485 116905623997744033930733)
                ·
                  rfl

theorem cell19_384198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_384198 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384198 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384198 prefixEnd_384198 := by exact prefixLift 384198
  have htrace : WordTrace (prefixWord ++ tailWord_384198) baseStart_384198 baseEnd_384198 := by
    simpa [prefixWord, tailWord_384198, baseEnd_384198] using wordTrace_append hprefix tailTrace_384198
  have hstable : (prefixWord ++ tailWord_384198).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384198).length < 2 ^ (prefixWord ++ tailWord_384198).sum := by decide
  have hdescent : baseEnd_384198 < baseStart_384198 := by decide
  rcases family_descends (prefixWord ++ tailWord_384198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384202 : List Nat := [3, 1, 2, 1, 3, 4, 2, 3]
def baseStart_384202 : Nat := 118140960795 + 384202 * 2 ^ 59
def prefixEnd_384202 : Nat := 4983230072969 + 3 ^ 40 * 384202 * 2
def baseEnd_384202 : Nat := 116906841137073209841833

theorem tailTrace_384202 : CollatzResearch.WordTrace tailWord_384202 prefixEnd_384202 116906841137073209841833 := by
  unfold tailWord_384202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503249538527311330678715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9341998769406163548476573 3503249538527311330678715)
  ·
    refine ⟨5254874307790966996018073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3503249538527311330678715 5254874307790966996018073)
    ·
      refine ⟨3941155730843225247013555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5254874307790966996018073 3941155730843225247013555)
      ·
        refine ⟨5911733596264837870520333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941155730843225247013555 5911733596264837870520333)
        ·
          refine ⟨2216900098599314201445125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5911733596264837870520333 2216900098599314201445125)
          ·
            refine ⟨415668768487371412770961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2216900098599314201445125 415668768487371412770961)
            ·
              refine ⟨311751576365528559578221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415668768487371412770961 311751576365528559578221)
              ·
                refine ⟨116906841137073209841833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311751576365528559578221 116906841137073209841833)
                ·
                  rfl

theorem cell19_384202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_384202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384202 prefixEnd_384202 := by exact prefixLift 384202
  have htrace : WordTrace (prefixWord ++ tailWord_384202) baseStart_384202 baseEnd_384202 := by
    simpa [prefixWord, tailWord_384202, baseEnd_384202] using wordTrace_append hprefix tailTrace_384202
  have hstable : (prefixWord ++ tailWord_384202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384202).length < 2 ^ (prefixWord ++ tailWord_384202).sum := by decide
  have hdescent : baseEnd_384202 < baseStart_384202 := by decide
  rcases family_descends (prefixWord ++ tailWord_384202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384221 : List Nat := [1, 4, 3, 2, 2, 2, 5]
def baseStart_384221 : Nat := 118140960795 + 384221 * 2 ^ 59
def prefixEnd_384221 : Nat := 4983230072969 + 3 ^ 40 * 384221 * 2
def baseEnd_384221 : Nat := 38970874182962265139853

theorem tailTrace_384221 : CollatzResearch.WordTrace tailWord_384221 prefixEnd_384221 38970874182962265139853 := by
  unfold tailWord_384221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013691141040411567656517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9342460760693607711771011 14013691141040411567656517)
  ·
    refine ⟨2627567088945077168935597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14013691141040411567656517 2627567088945077168935597)
    ·
      refine ⟨985337658354403938350849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2627567088945077168935597 985337658354403938350849)
      ·
        refine ⟨739003243765802953763137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 985337658354403938350849 739003243765802953763137)
        ·
          refine ⟨554252432824352215322353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739003243765802953763137 554252432824352215322353)
          ·
            refine ⟨415689324618264161491765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554252432824352215322353 415689324618264161491765)
            ·
              refine ⟨38970874182962265139853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 415689324618264161491765 38970874182962265139853)
              ·
                rfl

theorem cell19_384221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_384221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384221 prefixEnd_384221 := by exact prefixLift 384221
  have htrace : WordTrace (prefixWord ++ tailWord_384221) baseStart_384221 baseEnd_384221 := by
    simpa [prefixWord, tailWord_384221, baseEnd_384221] using wordTrace_append hprefix tailTrace_384221
  have hstable : (prefixWord ++ tailWord_384221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384221).length < 2 ^ (prefixWord ++ tailWord_384221).sum := by decide
  have hdescent : baseEnd_384221 < baseStart_384221 := by decide
  rcases family_descends (prefixWord ++ tailWord_384221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384225 : List Nat := [1, 2, 3, 1, 3, 2, 7]
def baseStart_384225 : Nat := 118140960795 + 384225 * 2 ^ 59
def prefixEnd_384225 : Nat := 4983230072969 + 3 ^ 40 * 384225 * 2
def baseEnd_384225 : Nat := 38971279896071990443553

theorem tailTrace_384225 : CollatzResearch.WordTrace tailWord_384225 prefixEnd_384225 38971279896071990443553 := by
  unfold tailWord_384225
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013837033025920250802129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9342558022017280167201419 14013837033025920250802129)
  ·
    refine ⟨10510377774769440188101597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14013837033025920250802129 10510377774769440188101597)
    ·
      refine ⟨3941391665538540070538099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10510377774769440188101597 3941391665538540070538099)
      ·
        refine ⟨5912087498307810105807149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941391665538540070538099 5912087498307810105807149)
        ·
          refine ⟨2217032811865428789677681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5912087498307810105807149 2217032811865428789677681)
          ·
            refine ⟨1662774608899071592258261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2217032811865428789677681 1662774608899071592258261)
            ·
              refine ⟨38971279896071990443553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1662774608899071592258261 38971279896071990443553)
              ·
                rfl

theorem cell19_384225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_384225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384225 prefixEnd_384225 := by exact prefixLift 384225
  have htrace : WordTrace (prefixWord ++ tailWord_384225) baseStart_384225 baseEnd_384225 := by
    simpa [prefixWord, tailWord_384225, baseEnd_384225] using wordTrace_append hprefix tailTrace_384225
  have hstable : (prefixWord ++ tailWord_384225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384225).length < 2 ^ (prefixWord ++ tailWord_384225).sum := by decide
  have hdescent : baseEnd_384225 < baseStart_384225 := by decide
  rcases family_descends (prefixWord ++ tailWord_384225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384282 : List Nat := [3, 1, 1, 3, 3, 8]
def baseStart_384282 : Nat := 118140960795 + 384282 * 2 ^ 59
def prefixEnd_384282 : Nat := 4983230072969 + 3 ^ 40 * 384282 * 2
def baseEnd_384282 : Nat := 12992353769295192007093

theorem tailTrace_384282 : CollatzResearch.WordTrace tailWord_384282 prefixEnd_384282 12992353769295192007093 := by
  unfold tailWord_384282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503978998454854746406775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9343943995879612657084733 3503978998454854746406775)
  ·
    refine ⟨5255968497682282119610163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3503978998454854746406775 5255968497682282119610163)
    ·
      refine ⟨7883952746523423179415245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5255968497682282119610163 7883952746523423179415245)
      ·
        refine ⟨2956482279946283692280717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7883952746523423179415245 2956482279946283692280717)
        ·
          refine ⟨1108680854979856384605269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2956482279946283692280717 1108680854979856384605269)
          ·
            refine ⟨12992353769295192007093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1108680854979856384605269 12992353769295192007093)
            ·
              rfl

theorem cell19_384282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 8].length) (baseStart_384282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384282 prefixEnd_384282 := by exact prefixLift 384282
  have htrace : WordTrace (prefixWord ++ tailWord_384282) baseStart_384282 baseEnd_384282 := by
    simpa [prefixWord, tailWord_384282, baseEnd_384282] using wordTrace_append hprefix tailTrace_384282
  have hstable : (prefixWord ++ tailWord_384282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384282).length < 2 ^ (prefixWord ++ tailWord_384282).sum := by decide
  have hdescent : baseEnd_384282 < baseStart_384282 := by decide
  rcases family_descends (prefixWord ++ tailWord_384282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384413 : List Nat := [1, 4, 2, 1, 3, 2, 2, 4]
def baseStart_384413 : Nat := 118140960795 + 384413 * 2 ^ 59
def prefixEnd_384413 : Nat := 4983230072969 + 3 ^ 40 * 384413 * 2
def baseEnd_384413 : Nat := 116971045236687239152369

theorem tailTrace_384413 : CollatzResearch.WordTrace tailWord_384413 prefixEnd_384413 116971045236687239152369 := by
  unfold tailWord_384413
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020693956344828358645893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9347129304229885572430595 14020693956344828358645893)
  ·
    refine ⟨2628880116814655317246105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14020693956344828358645893 2628880116814655317246105)
    ·
      refine ⟨1971660087610991487934579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2628880116814655317246105 1971660087610991487934579)
      ·
        refine ⟨2957490131416487231901869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971660087610991487934579 2957490131416487231901869)
        ·
          refine ⟨1109058799281182711963201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2957490131416487231901869 1109058799281182711963201)
          ·
            refine ⟨831794099460887033972401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1109058799281182711963201 831794099460887033972401)
            ·
              refine ⟨623845574595665275479301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831794099460887033972401 623845574595665275479301)
              ·
                refine ⟨116971045236687239152369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623845574595665275479301 116971045236687239152369)
                ·
                  rfl

theorem cell19_384413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_384413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384413 prefixEnd_384413 := by exact prefixLift 384413
  have htrace : WordTrace (prefixWord ++ tailWord_384413) baseStart_384413 baseEnd_384413 := by
    simpa [prefixWord, tailWord_384413, baseEnd_384413] using wordTrace_append hprefix tailTrace_384413
  have hstable : (prefixWord ++ tailWord_384413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384413).length < 2 ^ (prefixWord ++ tailWord_384413).sum := by decide
  have hdescent : baseEnd_384413 < baseStart_384413 := by decide
  rcases family_descends (prefixWord ++ tailWord_384413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384415 : List Nat := [1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_384415 : Nat := 118140960795 + 384415 * 2 ^ 59
def prefixEnd_384415 : Nat := 4983230072969 + 3 ^ 40 * 384415 * 2
def baseEnd_384415 : Nat := 116971653806351827107919

theorem tailTrace_384415 : CollatzResearch.WordTrace tailWord_384415 prefixEnd_384415 116971653806351827107919 := by
  unfold tailWord_384415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020766902337582700218699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9347177934891721800145799 14020766902337582700218699)
  ·
    refine ⟨21031150353506374050328049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14020766902337582700218699 21031150353506374050328049)
    ·
      refine ⟨15773362765129780537746037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21031150353506374050328049 15773362765129780537746037)
      ·
        refine ⟨1478752759230916925413691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15773362765129780537746037 1478752759230916925413691)
        ·
          refine ⟨2218129138846375388120537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478752759230916925413691 2218129138846375388120537)
          ·
            refine ⟨1663596854134781541090403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2218129138846375388120537 1663596854134781541090403)
            ·
              refine ⟨2495395281202172311635605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663596854134781541090403 2495395281202172311635605)
              ·
                refine ⟨116971653806351827107919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2495395281202172311635605 116971653806351827107919)
                ·
                  rfl

theorem cell19_384415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_384415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384415 prefixEnd_384415 := by exact prefixLift 384415
  have htrace : WordTrace (prefixWord ++ tailWord_384415) baseStart_384415 baseEnd_384415 := by
    simpa [prefixWord, tailWord_384415, baseEnd_384415] using wordTrace_append hprefix tailTrace_384415
  have hstable : (prefixWord ++ tailWord_384415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384415).length < 2 ^ (prefixWord ++ tailWord_384415).sum := by decide
  have hdescent : baseEnd_384415 < baseStart_384415 := by decide
  rcases family_descends (prefixWord ++ tailWord_384415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384468 : List Nat := [2, 4, 1, 2, 3, 2, 1, 4]
def baseStart_384468 : Nat := 118140960795 + 384468 * 2 ^ 59
def prefixEnd_384468 : Nat := 4983230072969 + 3 ^ 40 * 384468 * 2
def baseEnd_384468 : Nat := 116987780902463407929997

theorem tailTrace_384468 : CollatzResearch.WordTrace tailWord_384468 prefixEnd_384468 116987780902463407929997 := by
  unfold tailWord_384468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011349985572786375949029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9348466647430381834598705 7011349985572786375949029)
  ·
    refine ⟨1314628122294897445490443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7011349985572786375949029 1314628122294897445490443)
    ·
      refine ⟨1971942183442346168235665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314628122294897445490443 1971942183442346168235665)
      ·
        refine ⟨1478956637581759626176749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1971942183442346168235665 1478956637581759626176749)
        ·
          refine ⟨554608739093159859816281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1478956637581759626176749 554608739093159859816281)
          ·
            refine ⟨415956554319869894862211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554608739093159859816281 415956554319869894862211)
            ·
              refine ⟨623934831479804842293317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415956554319869894862211 623934831479804842293317)
              ·
                refine ⟨116987780902463407929997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623934831479804842293317 116987780902463407929997)
                ·
                  rfl

theorem cell19_384468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_384468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384468 prefixEnd_384468 := by exact prefixLift 384468
  have htrace : WordTrace (prefixWord ++ tailWord_384468) baseStart_384468 baseEnd_384468 := by
    simpa [prefixWord, tailWord_384468, baseEnd_384468] using wordTrace_append hprefix tailTrace_384468
  have hstable : (prefixWord ++ tailWord_384468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384468).length < 2 ^ (prefixWord ++ tailWord_384468).sum := by decide
  have hdescent : baseEnd_384468 < baseStart_384468 := by decide
  rcases family_descends (prefixWord ++ tailWord_384468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384472 : List Nat := [2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_384472 : Nat := 118140960795 + 384472 * 2 ^ 59
def prefixEnd_384472 : Nat := 4983230072969 + 3 ^ 40 * 384472 * 2
def baseEnd_384472 : Nat := 116988998041792583841097

theorem tailTrace_384472 : CollatzResearch.WordTrace tailWord_384472 prefixEnd_384472 116988998041792583841097 := by
  unfold tailWord_384472
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011422931565540717521835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9348563908754054290029113 7011422931565540717521835)
  ·
    refine ⟨10517134397348311076282753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7011422931565540717521835 10517134397348311076282753)
    ·
      refine ⟨7887850798011233307212065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10517134397348311076282753 7887850798011233307212065)
      ·
        refine ⟨5915888098508424980409049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7887850798011233307212065 5915888098508424980409049)
        ·
          refine ⟨4436916073881318735306787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5915888098508424980409049 4436916073881318735306787)
          ·
            refine ⟨6655374110821978102960181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436916073881318735306787 6655374110821978102960181)
            ·
              refine ⟨623941322889560447152517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6655374110821978102960181 623941322889560447152517)
              ·
                refine ⟨116988998041792583841097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623941322889560447152517 116988998041792583841097)
                ·
                  rfl

theorem cell19_384472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_384472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384472 prefixEnd_384472 := by exact prefixLift 384472
  have htrace : WordTrace (prefixWord ++ tailWord_384472) baseStart_384472 baseEnd_384472 := by
    simpa [prefixWord, tailWord_384472, baseEnd_384472] using wordTrace_append hprefix tailTrace_384472
  have hstable : (prefixWord ++ tailWord_384472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384472).length < 2 ^ (prefixWord ++ tailWord_384472).sum := by decide
  have hdescent : baseEnd_384472 < baseStart_384472 := by decide
  rcases family_descends (prefixWord ++ tailWord_384472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384544 : List Nat := [2, 1, 1, 6, 1, 3, 2, 3]
def baseStart_384544 : Nat := 118140960795 + 384544 * 2 ^ 59
def prefixEnd_384544 : Nat := 4983230072969 + 3 ^ 40 * 384544 * 2
def baseEnd_384544 : Nat := 117010906549717750240901

theorem tailTrace_384544 : CollatzResearch.WordTrace tailWord_384544 prefixEnd_384544 117010906549717750240901 := by
  unfold tailWord_384544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012735959435118865832343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9350314612580158487776457 7012735959435118865832343)
  ·
    refine ⟨10519103939152678298748515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012735959435118865832343 10519103939152678298748515)
    ·
      refine ⟨15778655908729017448122773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10519103939152678298748515 15778655908729017448122773)
      ·
        refine ⟨739624495721672692880755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15778655908729017448122773 739624495721672692880755)
        ·
          refine ⟨1109436743582509039321133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739624495721672692880755 1109436743582509039321133)
          ·
            refine ⟨416038778843440889745425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1109436743582509039321133 416038778843440889745425)
            ·
              refine ⟨312029084132580667309069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416038778843440889745425 312029084132580667309069)
              ·
                refine ⟨117010906549717750240901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312029084132580667309069 117010906549717750240901)
                ·
                  rfl

theorem cell19_384544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_384544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384544 prefixEnd_384544 := by exact prefixLift 384544
  have htrace : WordTrace (prefixWord ++ tailWord_384544) baseStart_384544 baseEnd_384544 := by
    simpa [prefixWord, tailWord_384544, baseEnd_384544] using wordTrace_append hprefix tailTrace_384544
  have hstable : (prefixWord ++ tailWord_384544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384544).length < 2 ^ (prefixWord ++ tailWord_384544).sum := by decide
  have hdescent : baseEnd_384544 < baseStart_384544 := by decide
  rcases family_descends (prefixWord ++ tailWord_384544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384546 : List Nat := [3, 3, 1, 1, 1, 1, 6, 3]
def baseStart_384546 : Nat := 118140960795 + 384546 * 2 ^ 59
def prefixEnd_384546 : Nat := 4983230072969 + 3 ^ 40 * 384546 * 2
def baseEnd_384546 : Nat := 117011515119382338196451

theorem tailTrace_384546 : CollatzResearch.WordTrace tailWord_384546 prefixEnd_384546 117011515119382338196451 := by
  unfold tailWord_384546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506386216215748018309373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9350363243241994715491661 3506386216215748018309373)
  ·
    refine ⟨1314894831080905506866015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3506386216215748018309373 1314894831080905506866015)
    ·
      refine ⟨1972342246621358260299023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1314894831080905506866015 1972342246621358260299023)
      ·
        refine ⟨2958513369932037390448535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972342246621358260299023 2958513369932037390448535)
        ·
          refine ⟨4437770054898056085672803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958513369932037390448535 4437770054898056085672803)
          ·
            refine ⟨6656655082347084128509205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437770054898056085672803 6656655082347084128509205)
            ·
              refine ⟨312030706985019568523869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6656655082347084128509205 312030706985019568523869)
              ·
                refine ⟨117011515119382338196451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312030706985019568523869 117011515119382338196451)
                ·
                  rfl

theorem cell19_384546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_384546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384546 prefixEnd_384546 := by exact prefixLift 384546
  have htrace : WordTrace (prefixWord ++ tailWord_384546) baseStart_384546 baseEnd_384546 := by
    simpa [prefixWord, tailWord_384546, baseEnd_384546] using wordTrace_append hprefix tailTrace_384546
  have hstable : (prefixWord ++ tailWord_384546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384546).length < 2 ^ (prefixWord ++ tailWord_384546).sum := by decide
  have hdescent : baseEnd_384546 < baseStart_384546 := by decide
  rcases family_descends (prefixWord ++ tailWord_384546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384567 : List Nat := [1, 1, 3, 1, 2, 6, 5]
def baseStart_384567 : Nat := 118140960795 + 384567 * 2 ^ 59
def prefixEnd_384567 : Nat := 4983230072969 + 3 ^ 40 * 384567 * 2
def baseEnd_384567 : Nat := 39005968366953503909909

theorem tailTrace_384567 : CollatzResearch.WordTrace tailWord_384567 prefixEnd_384567 39005968366953503909909 := by
  unfold tailWord_384567
  simp only [CollatzResearch.WordTrace]
  refine ⟨14026310797786912659751955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9350873865191275106501303 14026310797786912659751955)
  ·
    refine ⟨21039466196680368989627933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14026310797786912659751955 21039466196680368989627933)
    ·
      refine ⟨7889799823755138371110475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21039466196680368989627933 7889799823755138371110475)
      ·
        refine ⟨11834699735632707556665713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889799823755138371110475 11834699735632707556665713)
        ·
          refine ⟨8876024801724530667499285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11834699735632707556665713 8876024801724530667499285)
          ·
            refine ⟨416063662580837375039029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8876024801724530667499285 416063662580837375039029)
            ·
              refine ⟨39005968366953503909909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 416063662580837375039029 39005968366953503909909)
              ·
                rfl

theorem cell19_384567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 5].length) (baseStart_384567 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384567 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384567 prefixEnd_384567 := by exact prefixLift 384567
  have htrace : WordTrace (prefixWord ++ tailWord_384567) baseStart_384567 baseEnd_384567 := by
    simpa [prefixWord, tailWord_384567, baseEnd_384567] using wordTrace_append hprefix tailTrace_384567
  have hstable : (prefixWord ++ tailWord_384567).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384567).length < 2 ^ (prefixWord ++ tailWord_384567).sum := by decide
  have hdescent : baseEnd_384567 < baseStart_384567 := by decide
  rcases family_descends (prefixWord ++ tailWord_384567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384586 : List Nat := [3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_384586 : Nat := 118140960795 + 384586 * 2 ^ 59
def prefixEnd_384586 : Nat := 4983230072969 + 3 ^ 40 * 384586 * 2
def baseEnd_384586 : Nat := 117023686512674097307453

theorem tailTrace_384586 : CollatzResearch.WordTrace tailWord_384586 prefixEnd_384586 117023686512674097307453 := by
  unfold tailWord_384586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506750946179519726173403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9351335856478719269795741 3506750946179519726173403)
  ·
    refine ⟨5260126419269279589260105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3506750946179519726173403 5260126419269279589260105)
    ·
      refine ⟨3945094814451959691945079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5260126419269279589260105 3945094814451959691945079)
      ·
        refine ⟨5917642221677939537917619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3945094814451959691945079 5917642221677939537917619)
        ·
          refine ⟨8876463332516909306876429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917642221677939537917619 8876463332516909306876429)
          ·
            refine ⟨3328673749693840990078661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8876463332516909306876429 3328673749693840990078661)
            ·
              refine ⟨624126328067595185639749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3328673749693840990078661 624126328067595185639749)
              ·
                refine ⟨117023686512674097307453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624126328067595185639749 117023686512674097307453)
                ·
                  rfl

theorem cell19_384586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_384586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384586 prefixEnd_384586 := by exact prefixLift 384586
  have htrace : WordTrace (prefixWord ++ tailWord_384586) baseStart_384586 baseEnd_384586 := by
    simpa [prefixWord, tailWord_384586, baseEnd_384586] using wordTrace_append hprefix tailTrace_384586
  have hstable : (prefixWord ++ tailWord_384586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384586).length < 2 ^ (prefixWord ++ tailWord_384586).sum := by decide
  have hdescent : baseEnd_384586 < baseStart_384586 := by decide
  rcases family_descends (prefixWord ++ tailWord_384586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384622 : List Nat := [4, 1, 2, 2, 4, 6]
def baseStart_384622 : Nat := 118140960795 + 384622 * 2 ^ 59
def prefixEnd_384622 : Nat := 4983230072969 + 3 ^ 40 * 384622 * 2
def baseEnd_384622 : Nat := 13003848974070742278595

theorem tailTrace_384622 : CollatzResearch.WordTrace tailWord_384622 prefixEnd_384622 13003848974070742278595 := by
  unfold tailWord_384622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753539601573457131625515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9352211208391771368669413 1753539601573457131625515)
  ·
    refine ⟨2630309402360185697438273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1753539601573457131625515 2630309402360185697438273)
    ·
      refine ⟨1972732051770139273078705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2630309402360185697438273 1972732051770139273078705)
      ·
        refine ⟨1479549038827604454809029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972732051770139273078705 1479549038827604454809029)
        ·
          refine ⟨277415444780175835276693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1479549038827604454809029 277415444780175835276693)
          ·
            refine ⟨13003848974070742278595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277415444780175835276693 13003848974070742278595)
            ·
              rfl

theorem cell19_384622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_384622 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384622 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384622 prefixEnd_384622 := by exact prefixLift 384622
  have htrace : WordTrace (prefixWord ++ tailWord_384622) baseStart_384622 baseEnd_384622 := by
    simpa [prefixWord, tailWord_384622, baseEnd_384622] using wordTrace_append hprefix tailTrace_384622
  have hstable : (prefixWord ++ tailWord_384622).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384622).length < 2 ^ (prefixWord ++ tailWord_384622).sum := by decide
  have hdescent : baseEnd_384622 < baseStart_384622 := by decide
  rcases family_descends (prefixWord ++ tailWord_384622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384641 : List Nat := [1, 2, 4, 2, 1, 4, 1, 4]
def baseStart_384641 : Nat := 118140960795 + 384641 * 2 ^ 59
def prefixEnd_384641 : Nat := 4983230072969 + 3 ^ 40 * 384641 * 2
def baseEnd_384641 : Nat := 117040422178450266085081

theorem tailTrace_384641 : CollatzResearch.WordTrace tailWord_384641 prefixEnd_384641 117040422178450266085081 := by
  unfold tailWord_384641
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029009799518823297945777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9352673199679215531963851 14029009799518823297945777)
  ·
    refine ⟨10521757349639117473459333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14029009799518823297945777 10521757349639117473459333)
    ·
      refine ⟨1972829503057334526273625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10521757349639117473459333 1972829503057334526273625)
      ·
        refine ⟨1479622127293000894705219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972829503057334526273625 1479622127293000894705219)
        ·
          refine ⟨2219433190939501342057829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479622127293000894705219 2219433190939501342057829)
          ·
            refine ⟨416143723301156501635843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2219433190939501342057829 416143723301156501635843)
            ·
              refine ⟨624215584951734752453765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416143723301156501635843 624215584951734752453765)
              ·
                refine ⟨117040422178450266085081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 624215584951734752453765 117040422178450266085081)
                ·
                  rfl

theorem cell19_384641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_384641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384641 prefixEnd_384641 := by exact prefixLift 384641
  have htrace : WordTrace (prefixWord ++ tailWord_384641) baseStart_384641 baseEnd_384641 := by
    simpa [prefixWord, tailWord_384641, baseEnd_384641] using wordTrace_append hprefix tailTrace_384641
  have hstable : (prefixWord ++ tailWord_384641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384641).length < 2 ^ (prefixWord ++ tailWord_384641).sum := by decide
  have hdescent : baseEnd_384641 < baseStart_384641 := by decide
  rcases family_descends (prefixWord ++ tailWord_384641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384658 : List Nat := [3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_384658 : Nat := 118140960795 + 384658 * 2 ^ 59
def prefixEnd_384658 : Nat := 4983230072969 + 3 ^ 40 * 384658 * 2
def baseEnd_384658 : Nat := 117045595020599263707257

theorem tailTrace_384658 : CollatzResearch.WordTrace tailWord_384658 prefixEnd_384658 117045595020599263707257 := by
  unfold tailWord_384658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507407460114308800328657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9353086560304823467543085 3507407460114308800328657)
  ·
    refine ⟨2630555595085731600246493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3507407460114308800328657 2630555595085731600246493)
    ·
      refine ⟨986458348157149350092435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2630555595085731600246493 986458348157149350092435)
      ·
        refine ⟨1479687522235724025138653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986458348157149350092435 1479687522235724025138653)
        ·
          refine ⟨554882820838396509426995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1479687522235724025138653 554882820838396509426995)
          ·
            refine ⟨832324231257594764140493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554882820838396509426995 832324231257594764140493)
            ·
              refine ⟨312121586721598036552685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832324231257594764140493 312121586721598036552685)
              ·
                refine ⟨117045595020599263707257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312121586721598036552685 117045595020599263707257)
                ·
                  rfl

theorem cell19_384658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_384658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384658 prefixEnd_384658 := by exact prefixLift 384658
  have htrace : WordTrace (prefixWord ++ tailWord_384658) baseStart_384658 baseEnd_384658 := by
    simpa [prefixWord, tailWord_384658, baseEnd_384658] using wordTrace_append hprefix tailTrace_384658
  have hstable : (prefixWord ++ tailWord_384658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384658).length < 2 ^ (prefixWord ++ tailWord_384658).sum := by decide
  have hdescent : baseEnd_384658 < baseStart_384658 := by decide
  rcases family_descends (prefixWord ++ tailWord_384658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384759 : List Nat := [1, 1, 3, 1, 1, 1, 5, 6]
def baseStart_384759 : Nat := 118140960795 + 384759 * 2 ^ 59
def prefixEnd_384759 : Nat := 4983230072969 + 3 ^ 40 * 384759 * 2
def baseEnd_384759 : Nat := 117076327788660955462537

theorem tailTrace_384759 : CollatzResearch.WordTrace tailWord_384759 prefixEnd_384759 117076327788660955462537 := by
  unfold tailWord_384759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14033313613091329450741331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9355542408727552967160887 14033313613091329450741331)
  ·
    refine ⟨21049970419636994176111997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14033313613091329450741331 21049970419636994176111997)
    ·
      refine ⟨7893738907363872816041999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21049970419636994176111997 7893738907363872816041999)
      ·
        refine ⟨11840608361045809224062999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7893738907363872816041999 11840608361045809224062999)
        ·
          refine ⟨17760912541568713836094499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11840608361045809224062999 17760912541568713836094499)
          ·
            refine ⟨26641368812353070754141749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17760912541568713836094499 26641368812353070754141749)
            ·
              refine ⟨2497628326158100383200789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26641368812353070754141749 2497628326158100383200789)
              ·
                refine ⟨117076327788660955462537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2497628326158100383200789 117076327788660955462537)
                ·
                  rfl

theorem cell19_384759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_384759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384759 prefixEnd_384759 := by exact prefixLift 384759
  have htrace : WordTrace (prefixWord ++ tailWord_384759) baseStart_384759 baseEnd_384759 := by
    simpa [prefixWord, tailWord_384759, baseEnd_384759] using wordTrace_append hprefix tailTrace_384759
  have hstable : (prefixWord ++ tailWord_384759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384759).length < 2 ^ (prefixWord ++ tailWord_384759).sum := by decide
  have hdescent : baseEnd_384759 < baseStart_384759 := by decide
  rcases family_descends (prefixWord ++ tailWord_384759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384797 : List Nat := [1, 4, 2, 12]
def baseStart_384797 : Nat := 118140960795 + 384797 * 2 ^ 59
def prefixEnd_384797 : Nat := 4983230072969 + 3 ^ 40 * 384797 * 2
def baseEnd_384797 : Nat := 1445529513731952180469

theorem tailTrace_384797 : CollatzResearch.WordTrace tailWord_384797 prefixEnd_384797 1445529513731952180469 := by
  unfold tailWord_384797
  simp only [CollatzResearch.WordTrace]
  refine ⟨14034699586953661940624645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9356466391302441293749763 14034699586953661940624645)
  ·
    refine ⟨2631506172553811613867121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14034699586953661940624645 2631506172553811613867121)
    ·
      refine ⟨1973629629415358710400341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2631506172553811613867121 1973629629415358710400341)
      ·
        refine ⟨1445529513731952180469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1973629629415358710400341 1445529513731952180469)
        ·
          rfl

theorem cell19_384797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 12].length) (baseStart_384797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384797 prefixEnd_384797 := by exact prefixLift 384797
  have htrace : WordTrace (prefixWord ++ tailWord_384797) baseStart_384797 baseEnd_384797 := by
    simpa [prefixWord, tailWord_384797, baseEnd_384797] using wordTrace_append hprefix tailTrace_384797
  have hstable : (prefixWord ++ tailWord_384797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384797).length < 2 ^ (prefixWord ++ tailWord_384797).sum := by decide
  have hdescent : baseEnd_384797 < baseStart_384797 := by decide
  rcases family_descends (prefixWord ++ tailWord_384797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384831 : List Nat := [1, 1, 2, 2, 6, 1, 3, 3]
def baseStart_384831 : Nat := 118140960795 + 384831 * 2 ^ 59
def prefixEnd_384831 : Nat := 4983230072969 + 3 ^ 40 * 384831 * 2
def baseEnd_384831 : Nat := 117098236296586121862341

theorem tailTrace_384831 : CollatzResearch.WordTrace tailWord_384831 prefixEnd_384831 117098236296586121862341 := by
  unfold tailWord_384831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14035939668830485747362347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9357293112553657164908231 14035939668830485747362347)
  ·
    refine ⟨21053909503245728621043521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14035939668830485747362347 21053909503245728621043521)
    ·
      refine ⟨15790432127434296465782641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21053909503245728621043521 15790432127434296465782641)
      ·
        refine ⟨11842824095575722349336981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15790432127434296465782641 11842824095575722349336981)
        ·
          refine ⟨555132379480111985125171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11842824095575722349336981 555132379480111985125171)
          ·
            refine ⟨832698569220167977687757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 555132379480111985125171 832698569220167977687757)
            ·
              refine ⟨312261963457562991632909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 832698569220167977687757 312261963457562991632909)
              ·
                refine ⟨117098236296586121862341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312261963457562991632909 117098236296586121862341)
                ·
                  rfl

theorem cell19_384831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 3].length) (baseStart_384831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384831 prefixEnd_384831 := by exact prefixLift 384831
  have htrace : WordTrace (prefixWord ++ tailWord_384831) baseStart_384831 baseEnd_384831 := by
    simpa [prefixWord, tailWord_384831, baseEnd_384831] using wordTrace_append hprefix tailTrace_384831
  have hstable : (prefixWord ++ tailWord_384831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384831).length < 2 ^ (prefixWord ++ tailWord_384831).sum := by decide
  have hdescent : baseEnd_384831 < baseStart_384831 := by decide
  rcases family_descends (prefixWord ++ tailWord_384831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384852 : List Nat := [2, 4, 1, 1, 3, 2, 6]
def baseStart_384852 : Nat := 118140960795 + 384852 * 2 ^ 59
def prefixEnd_384852 : Nat := 4983230072969 + 3 ^ 40 * 384852 * 2
def baseEnd_384852 : Nat := 39034875426021431798539

theorem tailTrace_384852 : CollatzResearch.WordTrace tailWord_384852 prefixEnd_384852 39034875426021431798539 := by
  unfold tailWord_384852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018352800877203166938405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9357803734502937555917873 7018352800877203166938405)
  ·
    refine ⟨1315941150164475593800951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7018352800877203166938405 1315941150164475593800951)
    ·
      refine ⟨1973911725246713390701427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315941150164475593800951 1973911725246713390701427)
      ·
        refine ⟨2960867587870070086052141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973911725246713390701427 2960867587870070086052141)
        ·
          refine ⟨1110325345451276282269553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2960867587870070086052141 1110325345451276282269553)
          ·
            refine ⟨832744009088457211702165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1110325345451276282269553 832744009088457211702165)
            ·
              refine ⟨39034875426021431798539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 832744009088457211702165 39034875426021431798539)
              ·
                rfl

theorem cell19_384852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_384852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384852 prefixEnd_384852 := by exact prefixLift 384852
  have htrace : WordTrace (prefixWord ++ tailWord_384852) baseStart_384852 baseEnd_384852 := by
    simpa [prefixWord, tailWord_384852, baseEnd_384852] using wordTrace_append hprefix tailTrace_384852
  have hstable : (prefixWord ++ tailWord_384852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384852).length < 2 ^ (prefixWord ++ tailWord_384852).sum := by decide
  have hdescent : baseEnd_384852 < baseStart_384852 := by decide
  rcases family_descends (prefixWord ++ tailWord_384852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384890 : List Nat := [3, 1, 1, 1, 1, 1, 8, 3]
def baseStart_384890 : Nat := 118140960795 + 384890 * 2 ^ 59
def prefixEnd_384890 : Nat := 4983230072969 + 3 ^ 40 * 384890 * 2
def baseEnd_384890 : Nat := 117116189101691466551069

theorem tailTrace_384890 : CollatzResearch.WordTrace tailWord_384890 prefixEnd_384890 117116189101691466551069 := by
  unfold tailWord_384890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509522893904184705940031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9358727717077825882506749 3509522893904184705940031)
  ·
    refine ⟨5264284340856277058910047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509522893904184705940031 5264284340856277058910047)
    ·
      refine ⟨7896426511284415588365071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264284340856277058910047 7896426511284415588365071)
      ·
        refine ⟨11844639766926623382547607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896426511284415588365071 11844639766926623382547607)
        ·
          refine ⟨17766959650389935073821411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11844639766926623382547607 17766959650389935073821411)
          ·
            refine ⟨26650439475584902610732117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17766959650389935073821411 26650439475584902610732117)
            ·
              refine ⟨312309837604510577469517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 26650439475584902610732117 312309837604510577469517)
              ·
                refine ⟨117116189101691466551069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312309837604510577469517 117116189101691466551069)
                ·
                  rfl

theorem cell19_384890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_384890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384890 prefixEnd_384890 := by exact prefixLift 384890
  have htrace : WordTrace (prefixWord ++ tailWord_384890) baseStart_384890 baseEnd_384890 := by
    simpa [prefixWord, tailWord_384890, baseEnd_384890] using wordTrace_append hprefix tailTrace_384890
  have hstable : (prefixWord ++ tailWord_384890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384890).length < 2 ^ (prefixWord ++ tailWord_384890).sum := by decide
  have hdescent : baseEnd_384890 < baseStart_384890 := by decide
  rcases family_descends (prefixWord ++ tailWord_384890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384968 : List Nat := [2, 1, 3, 1, 4, 8]
def baseStart_384968 : Nat := 118140960795 + 384968 * 2 ^ 59
def prefixEnd_384968 : Nat := 4983230072969 + 3 ^ 40 * 384968 * 2
def baseEnd_384968 : Nat := 13015547035401155201947

theorem tailTrace_384968 : CollatzResearch.WordTrace tailWord_384968 prefixEnd_384968 13015547035401155201947 := by
  unfold tailWord_384968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020468234667079072549779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9360624312889438763399705 7020468234667079072549779)
  ·
    refine ⟨10530702352000618608824669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7020468234667079072549779 10530702352000618608824669)
    ·
      refine ⟨3949013382000231978309251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10530702352000618608824669 3949013382000231978309251)
      ·
        refine ⟨5923520073000347967463877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3949013382000231978309251 5923520073000347967463877)
        ·
          refine ⟨1110660013687565243899477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5923520073000347967463877 1110660013687565243899477)
          ·
            refine ⟨13015547035401155201947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1110660013687565243899477 13015547035401155201947)
            ·
              rfl

theorem cell19_384968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 8].length) (baseStart_384968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_384968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_384968 prefixEnd_384968 := by exact prefixLift 384968
  have htrace : WordTrace (prefixWord ++ tailWord_384968) baseStart_384968 baseEnd_384968 := by
    simpa [prefixWord, tailWord_384968, baseEnd_384968] using wordTrace_append hprefix tailTrace_384968
  have hstable : (prefixWord ++ tailWord_384968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384968).length < 2 ^ (prefixWord ++ tailWord_384968).sum := by decide
  have hdescent : baseEnd_384968 < baseStart_384968 := by decide
  rcases family_descends (prefixWord ++ tailWord_384968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385025 : List Nat := [1, 2, 4, 1, 2, 1, 8]
def baseStart_385025 : Nat := 118140960795 + 385025 * 2 ^ 59
def prefixEnd_385025 : Nat := 4983230072969 + 3 ^ 40 * 385025 * 2
def baseEnd_385025 : Nat := 39052422518017051183567

theorem tailTrace_385025 : CollatzResearch.WordTrace tailWord_385025 prefixEnd_385025 39052422518017051183567 := by
  unfold tailWord_385025
  simp only [CollatzResearch.WordTrace]
  refine ⟨14043015430127656879924529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9362010286751771253283019 14043015430127656879924529)
  ·
    refine ⟨10532261572595742659943397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14043015430127656879924529 10532261572595742659943397)
    ·
      refine ⟨1974799044861701748739387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10532261572595742659943397 1974799044861701748739387)
      ·
        refine ⟨2962198567292552623109081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974799044861701748739387 2962198567292552623109081)
        ·
          refine ⟨2221648925469414467331811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2962198567292552623109081 2221648925469414467331811)
          ·
            refine ⟨3332473388204121700997717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221648925469414467331811 3332473388204121700997717)
            ·
              refine ⟨39052422518017051183567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3332473388204121700997717 39052422518017051183567)
              ·
                rfl

theorem cell19_385025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 8].length) (baseStart_385025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385025 prefixEnd_385025 := by exact prefixLift 385025
  have htrace : WordTrace (prefixWord ++ tailWord_385025) baseStart_385025 baseEnd_385025 := by
    simpa [prefixWord, tailWord_385025, baseEnd_385025] using wordTrace_append hprefix tailTrace_385025
  have hstable : (prefixWord ++ tailWord_385025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385025).length < 2 ^ (prefixWord ++ tailWord_385025).sum := by decide
  have hdescent : baseEnd_385025 < baseStart_385025 := by decide
  rcases family_descends (prefixWord ++ tailWord_385025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385057 : List Nat := [1, 2, 3, 2, 5, 1, 2, 3]
def baseStart_385057 : Nat := 118140960795 + 385057 * 2 ^ 59
def prefixEnd_385057 : Nat := 4983230072969 + 3 ^ 40 * 385057 * 2
def baseEnd_385057 : Nat := 117167004668684560839503

theorem tailTrace_385057 : CollatzResearch.WordTrace tailWord_385057 prefixEnd_385057 117167004668684560839503 := by
  unfold tailWord_385057
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044182566011726345089425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9362788377341150896726283 14044182566011726345089425)
  ·
    refine ⟨10533136924508794758817069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14044182566011726345089425 10533136924508794758817069)
    ·
      refine ⟨3949926346690798034556401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10533136924508794758817069 3949926346690798034556401)
      ·
        refine ⟨2962444760018098525917301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3949926346690798034556401 2962444760018098525917301)
        ·
          refine ⟨277729196251696736804747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2962444760018098525917301 277729196251696736804747)
          ·
            refine ⟨416593794377545105207121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277729196251696736804747 416593794377545105207121)
            ·
              refine ⟨312445345783158828905341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416593794377545105207121 312445345783158828905341)
              ·
                refine ⟨117167004668684560839503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312445345783158828905341 117167004668684560839503)
                ·
                  rfl

theorem cell19_385057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 3].length) (baseStart_385057 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385057 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385057 prefixEnd_385057 := by exact prefixLift 385057
  have htrace : WordTrace (prefixWord ++ tailWord_385057) baseStart_385057 baseEnd_385057 := by
    simpa [prefixWord, tailWord_385057, baseEnd_385057] using wordTrace_append hprefix tailTrace_385057
  have hstable : (prefixWord ++ tailWord_385057).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385057).length < 2 ^ (prefixWord ++ tailWord_385057).sum := by decide
  have hdescent : baseEnd_385057 < baseStart_385057 := by decide
  rcases family_descends (prefixWord ++ tailWord_385057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385061 : List Nat := [1, 3, 1, 2, 2, 3, 4, 3]
def baseStart_385061 : Nat := 118140960795 + 385061 * 2 ^ 59
def prefixEnd_385061 : Nat := 4983230072969 + 3 ^ 40 * 385061 * 2
def baseEnd_385061 : Nat := 117168221808013736750603

theorem tailTrace_385061 : CollatzResearch.WordTrace tailWord_385061 prefixEnd_385061 117168221808013736750603 := by
  unfold tailWord_385061
  simp only [CollatzResearch.WordTrace]
  refine ⟨14044328457997235028235037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9362885638664823352156691 14044328457997235028235037)
  ·
    refine ⟨5266623171748963135588139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14044328457997235028235037 5266623171748963135588139)
    ·
      refine ⟨7899934757623444703382209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5266623171748963135588139 7899934757623444703382209)
      ·
        refine ⟨5924951068217583527536657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7899934757623444703382209 5924951068217583527536657)
        ·
          refine ⟨4443713301163187645652493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5924951068217583527536657 4443713301163187645652493)
          ·
            refine ⟨1666392487936195367119685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4443713301163187645652493 1666392487936195367119685)
            ·
              refine ⟨312448591488036631334941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1666392487936195367119685 312448591488036631334941)
              ·
                refine ⟨117168221808013736750603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312448591488036631334941 117168221808013736750603)
                ·
                  rfl

theorem cell19_385061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_385061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385061 prefixEnd_385061 := by exact prefixLift 385061
  have htrace : WordTrace (prefixWord ++ tailWord_385061) baseStart_385061 baseEnd_385061 := by
    simpa [prefixWord, tailWord_385061, baseEnd_385061] using wordTrace_append hprefix tailTrace_385061
  have hstable : (prefixWord ++ tailWord_385061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385061).length < 2 ^ (prefixWord ++ tailWord_385061).sum := by decide
  have hdescent : baseEnd_385061 < baseStart_385061 := by decide
  rcases family_descends (prefixWord ++ tailWord_385061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385076 : List Nat := [2, 5, 1, 2, 3, 1, 5]
def baseStart_385076 : Nat := 118140960795 + 385076 * 2 ^ 59
def prefixEnd_385076 : Nat := 4983230072969 + 3 ^ 40 * 385076 * 2
def baseEnd_385076 : Nat := 39057595360166048805743

theorem tailTrace_385076 : CollatzResearch.WordTrace tailWord_385076 prefixEnd_385076 39057595360166048805743 := by
  unfold tailWord_385076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022437776471446295015541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9363250368628595060020721 7022437776471446295015541)
  ·
    refine ⟨658353541544198090157707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7022437776471446295015541 658353541544198090157707)
    ·
      refine ⟨987530312316297135236561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658353541544198090157707 987530312316297135236561)
      ·
        refine ⟨740647734237222851427421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 987530312316297135236561 740647734237222851427421)
        ·
          refine ⟨277742900338958569285283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 740647734237222851427421 277742900338958569285283)
          ·
            refine ⟨416614350508437853927925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277742900338958569285283 416614350508437853927925)
            ·
              refine ⟨39057595360166048805743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 416614350508437853927925 39057595360166048805743)
              ·
                rfl

theorem cell19_385076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 5].length) (baseStart_385076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385076 prefixEnd_385076 := by exact prefixLift 385076
  have htrace : WordTrace (prefixWord ++ tailWord_385076) baseStart_385076 baseEnd_385076 := by
    simpa [prefixWord, tailWord_385076, baseEnd_385076] using wordTrace_append hprefix tailTrace_385076
  have hstable : (prefixWord ++ tailWord_385076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385076).length < 2 ^ (prefixWord ++ tailWord_385076).sum := by decide
  have hdescent : baseEnd_385076 < baseStart_385076 := by decide
  rcases family_descends (prefixWord ++ tailWord_385076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385080 : List Nat := [2, 1, 2, 1, 6, 2, 5]
def baseStart_385080 : Nat := 118140960795 + 385080 * 2 ^ 59
def prefixEnd_385080 : Nat := 4983230072969 + 3 ^ 40 * 385080 * 2
def baseEnd_385080 : Nat := 39058001073275774109443

theorem tailTrace_385080 : CollatzResearch.WordTrace tailWord_385080 prefixEnd_385080 39058001073275774109443 := by
  unfold tailWord_385080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022510722464200636588347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9363347629952267515451129 7022510722464200636588347)
  ·
    refine ⟨10533766083696300954882521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7022510722464200636588347 10533766083696300954882521)
    ·
      refine ⟨7900324562772225716161891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10533766083696300954882521 7900324562772225716161891)
      ·
        refine ⟨11850486844158338574242837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7900324562772225716161891 11850486844158338574242837)
        ·
          refine ⟨555491570819922120667633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11850486844158338574242837 555491570819922120667633)
          ·
            refine ⟨416618678114941590500725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555491570819922120667633 416618678114941590500725)
            ·
              refine ⟨39058001073275774109443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 416618678114941590500725 39058001073275774109443)
              ·
                rfl

theorem cell19_385080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 5].length) (baseStart_385080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385080 prefixEnd_385080 := by exact prefixLift 385080
  have htrace : WordTrace (prefixWord ++ tailWord_385080) baseStart_385080 baseEnd_385080 := by
    simpa [prefixWord, tailWord_385080, baseEnd_385080] using wordTrace_append hprefix tailTrace_385080
  have hstable : (prefixWord ++ tailWord_385080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385080).length < 2 ^ (prefixWord ++ tailWord_385080).sum := by decide
  have hdescent : baseEnd_385080 < baseStart_385080 := by decide
  rcases family_descends (prefixWord ++ tailWord_385080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385120 : List Nat := [2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_385120 : Nat := 118140960795 + 385120 * 2 ^ 59
def prefixEnd_385120 : Nat := 4983230072969 + 3 ^ 40 * 385120 * 2
def baseEnd_385120 : Nat := 117186174613119081439331

theorem tailTrace_385120 : CollatzResearch.WordTrace tailWord_385120 prefixEnd_385120 117186174613119081439331 := by
  unfold tailWord_385120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7023240182391744052316407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9364320243188992069755209 7023240182391744052316407)
  ·
    refine ⟨10534860273587616078474611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7023240182391744052316407 10534860273587616078474611)
    ·
      refine ⟨15802290410381424117711917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10534860273587616078474611 15802290410381424117711917)
      ·
        refine ⟨5925858903893034044141969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15802290410381424117711917 5925858903893034044141969)
        ·
          refine ⟨4444394177919775533106477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5925858903893034044141969 4444394177919775533106477)
          ·
            refine ⟨1666647816719915824914929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4444394177919775533106477 1666647816719915824914929)
            ·
              refine ⟨1249985862539936868686197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666647816719915824914929 1249985862539936868686197)
              ·
                refine ⟨117186174613119081439331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1249985862539936868686197 117186174613119081439331)
                ·
                  rfl

theorem cell19_385120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_385120 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385120 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385120 prefixEnd_385120 := by exact prefixLift 385120
  have htrace : WordTrace (prefixWord ++ tailWord_385120) baseStart_385120 baseEnd_385120 := by
    simpa [prefixWord, tailWord_385120, baseEnd_385120] using wordTrace_append hprefix tailTrace_385120
  have hstable : (prefixWord ++ tailWord_385120).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385120).length < 2 ^ (prefixWord ++ tailWord_385120).sum := by decide
  have hdescent : baseEnd_385120 < baseStart_385120 := by decide
  rcases family_descends (prefixWord ++ tailWord_385120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385228 : List Nat := [2, 2, 1, 6, 1, 2, 2, 3]
def baseStart_385228 : Nat := 118140960795 + 385228 * 2 ^ 59
def prefixEnd_385228 : Nat := 4983230072969 + 3 ^ 40 * 385228 * 2
def baseEnd_385228 : Nat := 117219037375006831039037

theorem tailTrace_385228 : CollatzResearch.WordTrace tailWord_385228 prefixEnd_385228 117219037375006831039037 := by
  unfold tailWord_385228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025209724196111274782169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9366946298928148366376225 7025209724196111274782169)
  ·
    refine ⟨5268907293147083456086627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7025209724196111274782169 5268907293147083456086627)
    ·
      refine ⟨7903360939720625184129941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5268907293147083456086627 7903360939720625184129941)
      ·
        refine ⟨370470044049404305506091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7903360939720625184129941 370470044049404305506091)
        ·
          refine ⟨555705066074106458259137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370470044049404305506091 555705066074106458259137)
          ·
            refine ⟨416778799555579843694353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555705066074106458259137 416778799555579843694353)
            ·
              refine ⟨312584099666684882770765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416778799555579843694353 312584099666684882770765)
              ·
                refine ⟨117219037375006831039037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312584099666684882770765 117219037375006831039037)
                ·
                  rfl

theorem cell19_385228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_385228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385228 prefixEnd_385228 := by exact prefixLift 385228
  have htrace : WordTrace (prefixWord ++ tailWord_385228) baseStart_385228 baseEnd_385228 := by
    simpa [prefixWord, tailWord_385228, baseEnd_385228] using wordTrace_append hprefix tailTrace_385228
  have hstable : (prefixWord ++ tailWord_385228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385228).length < 2 ^ (prefixWord ++ tailWord_385228).sum := by decide
  have hdescent : baseEnd_385228 < baseStart_385228 := by decide
  rcases family_descends (prefixWord ++ tailWord_385228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385230 : List Nat := [4, 1, 1, 1, 4, 3, 2, 3]
def baseStart_385230 : Nat := 118140960795 + 385230 * 2 ^ 59
def prefixEnd_385230 : Nat := 4983230072969 + 3 ^ 40 * 385230 * 2
def baseEnd_385230 : Nat := 117219645944671418994587

theorem tailTrace_385230 : CollatzResearch.WordTrace tailWord_385230 prefixEnd_385230 117219645944671418994587 := by
  unfold tailWord_385230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756311549298122111392143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9366994929589984594091429 1756311549298122111392143)
  ·
    refine ⟨2634467323947183167088215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1756311549298122111392143 2634467323947183167088215)
    ·
      refine ⟨3951700985920774750632323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2634467323947183167088215 3951700985920774750632323)
      ·
        refine ⟨5927551478881162125948485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3951700985920774750632323 5927551478881162125948485)
        ·
          refine ⟨1111415902290217898615341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5927551478881162125948485 1111415902290217898615341)
          ·
            refine ⟨416780963358831711980753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1111415902290217898615341 416780963358831711980753)
            ·
              refine ⟨312585722519123783985565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416780963358831711980753 312585722519123783985565)
              ·
                refine ⟨117219645944671418994587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312585722519123783985565 117219645944671418994587)
                ·
                  rfl

theorem cell19_385230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_385230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385230 prefixEnd_385230 := by exact prefixLift 385230
  have htrace : WordTrace (prefixWord ++ tailWord_385230) baseStart_385230 baseEnd_385230 := by
    simpa [prefixWord, tailWord_385230, baseEnd_385230] using wordTrace_append hprefix tailTrace_385230
  have hstable : (prefixWord ++ tailWord_385230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385230).length < 2 ^ (prefixWord ++ tailWord_385230).sum := by decide
  have hdescent : baseEnd_385230 < baseStart_385230 := by decide
  rcases family_descends (prefixWord ++ tailWord_385230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385253 : List Nat := [1, 3, 1, 4, 2, 1, 7]
def baseStart_385253 : Nat := 118140960795 + 385253 * 2 ^ 59
def prefixEnd_385253 : Nat := 4983230072969 + 3 ^ 40 * 385253 * 2
def baseEnd_385253 : Nat := 39075548165271393494471

theorem tailTrace_385253 : CollatzResearch.WordTrace tailWord_385253 prefixEnd_385253 39075548165271393494471 := by
  unfold tailWord_385253
  simp only [CollatzResearch.WordTrace]
  refine ⟨14051331273301651819224413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9367554182201101212816275 14051331273301651819224413)
  ·
    refine ⟨5269249227488119432209155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14051331273301651819224413 5269249227488119432209155)
    ·
      refine ⟨7903873841232179148313733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5269249227488119432209155 7903873841232179148313733)
      ·
        refine ⟨1481976345231033590308825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7903873841232179148313733 1481976345231033590308825)
        ·
          refine ⟨1111482258923275192731619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1481976345231033590308825 1111482258923275192731619)
          ·
            refine ⟨1667223388384912789097429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111482258923275192731619 1667223388384912789097429)
            ·
              refine ⟨39075548165271393494471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1667223388384912789097429 39075548165271393494471)
              ·
                rfl

theorem cell19_385253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 7].length) (baseStart_385253 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385253 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385253 prefixEnd_385253 := by exact prefixLift 385253
  have htrace : WordTrace (prefixWord ++ tailWord_385253) baseStart_385253 baseEnd_385253 := by
    simpa [prefixWord, tailWord_385253, baseEnd_385253] using wordTrace_append hprefix tailTrace_385253
  have hstable : (prefixWord ++ tailWord_385253).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385253).length < 2 ^ (prefixWord ++ tailWord_385253).sum := by decide
  have hdescent : baseEnd_385253 < baseStart_385253 := by decide
  rcases family_descends (prefixWord ++ tailWord_385253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385403 : List Nat := [1, 1, 1, 1, 1, 9, 2, 3]
def baseStart_385403 : Nat := 118140960795 + 385403 * 2 ^ 59
def prefixEnd_385403 : Nat := 4983230072969 + 3 ^ 40 * 385403 * 2
def baseEnd_385403 : Nat := 117272287220658277149671

theorem tailTrace_385403 : CollatzResearch.WordTrace tailWord_385403 prefixEnd_385403 117272287220658277149671 := by
  unfold tailWord_385403
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056802222758227437184863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9371201481838818291456575 14056802222758227437184863)
  ·
    refine ⟨21085203334137341155777295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14056802222758227437184863 21085203334137341155777295)
    ·
      refine ⟨31627805001206011733665943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21085203334137341155777295 31627805001206011733665943)
      ·
        refine ⟨47441707501809017600498915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31627805001206011733665943 47441707501809017600498915)
        ·
          refine ⟨71162561252713526400748373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47441707501809017600498915 71162561252713526400748373)
          ·
            refine ⟨416968132340118318754385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 71162561252713526400748373 416968132340118318754385)
            ·
              refine ⟨312726099255088739065789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416968132340118318754385 312726099255088739065789)
              ·
                refine ⟨117272287220658277149671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 312726099255088739065789 117272287220658277149671)
                ·
                  rfl

theorem cell19_385403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_385403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385403 prefixEnd_385403 := by exact prefixLift 385403
  have htrace : WordTrace (prefixWord ++ tailWord_385403) baseStart_385403 baseEnd_385403 := by
    simpa [prefixWord, tailWord_385403, baseEnd_385403] using wordTrace_append hprefix tailTrace_385403
  have hstable : (prefixWord ++ tailWord_385403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385403).length < 2 ^ (prefixWord ++ tailWord_385403).sum := by decide
  have hdescent : baseEnd_385403 < baseStart_385403 := by decide
  rcases family_descends (prefixWord ++ tailWord_385403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385405 : List Nat := [1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_385405 : Nat := 118140960795 + 385405 * 2 ^ 59
def prefixEnd_385405 : Nat := 4983230072969 + 3 ^ 40 * 385405 * 2
def baseEnd_385405 : Nat := 117272895790322865105221

theorem tailTrace_385405 : CollatzResearch.WordTrace tailWord_385405 prefixEnd_385405 117272895790322865105221 := by
  unfold tailWord_385405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056875168750981778757669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9371250112500654519171779 14056875168750981778757669)
  ·
    refine ⟨2635664094140809083517063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14056875168750981778757669 2635664094140809083517063)
    ·
      refine ⟨3953496141211213625275595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635664094140809083517063 3953496141211213625275595)
      ·
        refine ⟨5930244211816820437913393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3953496141211213625275595 5930244211816820437913393)
        ·
          refine ⟨4447683158862615328435045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5930244211816820437913393 4447683158862615328435045)
          ·
            refine ⟨833940592286740374081571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4447683158862615328435045 833940592286740374081571)
            ·
              refine ⟨1250910888430110561122357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833940592286740374081571 1250910888430110561122357)
              ·
                refine ⟨117272895790322865105221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250910888430110561122357 117272895790322865105221)
                ·
                  rfl

theorem cell19_385405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_385405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385405 prefixEnd_385405 := by exact prefixLift 385405
  have htrace : WordTrace (prefixWord ++ tailWord_385405) baseStart_385405 baseEnd_385405 := by
    simpa [prefixWord, tailWord_385405, baseEnd_385405] using wordTrace_append hprefix tailTrace_385405
  have hstable : (prefixWord ++ tailWord_385405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385405).length < 2 ^ (prefixWord ++ tailWord_385405).sum := by decide
  have hdescent : baseEnd_385405 < baseStart_385405 := by decide
  rcases family_descends (prefixWord ++ tailWord_385405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385407 : List Nat := [1, 1, 2, 2, 1, 1, 2, 9]
def baseStart_385407 : Nat := 118140960795 + 385407 * 2 ^ 59
def prefixEnd_385407 : Nat := 4983230072969 + 3 ^ 40 * 385407 * 2
def baseEnd_385407 : Nat := 117273504359987453060771

theorem tailTrace_385407 : CollatzResearch.WordTrace tailWord_385407 prefixEnd_385407 117273504359987453060771 := by
  unfold tailWord_385407
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056948114743736120330475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9371298743162490746886983 14056948114743736120330475)
  ·
    refine ⟨21085422172115604180495713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14056948114743736120330475 21085422172115604180495713)
    ·
      refine ⟨15814066629086703135371785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21085422172115604180495713 15814066629086703135371785)
      ·
        refine ⟨11860549971815027351528839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15814066629086703135371785 11860549971815027351528839)
        ·
          refine ⟨17790824957722541027293259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11860549971815027351528839 17790824957722541027293259)
          ·
            refine ⟨26686237436583811540939889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17790824957722541027293259 26686237436583811540939889)
            ·
              refine ⟨20014678077437858655704917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26686237436583811540939889 20014678077437858655704917)
              ·
                refine ⟨117273504359987453060771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20014678077437858655704917 117273504359987453060771)
                ·
                  rfl

theorem cell19_385407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_385407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385407 prefixEnd_385407 := by exact prefixLift 385407
  have htrace : WordTrace (prefixWord ++ tailWord_385407) baseStart_385407 baseEnd_385407 := by
    simpa [prefixWord, tailWord_385407, baseEnd_385407] using wordTrace_append hprefix tailTrace_385407
  have hstable : (prefixWord ++ tailWord_385407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385407).length < 2 ^ (prefixWord ++ tailWord_385407).sum := by decide
  have hdescent : baseEnd_385407 < baseStart_385407 := by decide
  rcases family_descends (prefixWord ++ tailWord_385407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385422 : List Nat := [4, 1, 1, 4, 1, 3, 5]
def baseStart_385422 : Nat := 118140960795 + 385422 * 2 ^ 59
def prefixEnd_385422 : Nat := 4983230072969 + 3 ^ 40 * 385422 * 2
def baseEnd_385422 : Nat := 39092689544157287575799

theorem tailTrace_385422 : CollatzResearch.WordTrace tailWord_385422 prefixEnd_385422 39092689544157287575799 := by
  unfold tailWord_385422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1757186901211174210265815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9371663473126262454751013 1757186901211174210265815)
  ·
    refine ⟨2635780351816761315398723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1757186901211174210265815 2635780351816761315398723)
    ·
      refine ⟨3953670527725141973098085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635780351816761315398723 3953670527725141973098085)
      ·
        refine ⟨741313223948464119955891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3953670527725141973098085 741313223948464119955891)
        ·
          refine ⟨1111969835922696179933837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741313223948464119955891 1111969835922696179933837)
          ·
            refine ⟨416988688471011067475189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1111969835922696179933837 416988688471011067475189)
            ·
              refine ⟨39092689544157287575799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 416988688471011067475189 39092689544157287575799)
              ·
                rfl

theorem cell19_385422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_385422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385422 prefixEnd_385422 := by exact prefixLift 385422
  have htrace : WordTrace (prefixWord ++ tailWord_385422) baseStart_385422 baseEnd_385422 := by
    simpa [prefixWord, tailWord_385422, baseEnd_385422] using wordTrace_append hprefix tailTrace_385422
  have hstable : (prefixWord ++ tailWord_385422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385422).length < 2 ^ (prefixWord ++ tailWord_385422).sum := by decide
  have hdescent : baseEnd_385422 < baseStart_385422 := by decide
  rcases family_descends (prefixWord ++ tailWord_385422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385443 : List Nat := [1, 1, 1, 4, 1, 5, 2, 4]
def baseStart_385443 : Nat := 118140960795 + 385443 * 2 ^ 59
def prefixEnd_385443 : Nat := 4983230072969 + 3 ^ 40 * 385443 * 2
def baseEnd_385443 : Nat := 117284458613950036260673

theorem tailTrace_385443 : CollatzResearch.WordTrace tailWord_385443 prefixEnd_385443 117284458613950036260673 := by
  unfold tailWord_385443
  simp only [CollatzResearch.WordTrace]
  refine ⟨14058261142613314268640983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9372174095075542845760655 14058261142613314268640983)
  ·
    refine ⟨21087391713919971402961475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14058261142613314268640983 21087391713919971402961475)
    ·
      refine ⟨31631087570879957104442213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21087391713919971402961475 31631087570879957104442213)
      ·
        refine ⟨5930828919539991957082915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31631087570879957104442213 5930828919539991957082915)
        ·
          refine ⟨8896243379309987935624373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930828919539991957082915 8896243379309987935624373)
          ·
            refine ⟨834022816810311368964785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8896243379309987935624373 834022816810311368964785)
            ·
              refine ⟨625517112607733526723589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834022816810311368964785 625517112607733526723589)
              ·
                refine ⟨117284458613950036260673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 625517112607733526723589 117284458613950036260673)
                ·
                  rfl

theorem cell19_385443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_385443 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385443 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385443 prefixEnd_385443 := by exact prefixLift 385443
  have htrace : WordTrace (prefixWord ++ tailWord_385443) baseStart_385443 baseEnd_385443 := by
    simpa [prefixWord, tailWord_385443, baseEnd_385443] using wordTrace_append hprefix tailTrace_385443
  have hstable : (prefixWord ++ tailWord_385443).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385443).length < 2 ^ (prefixWord ++ tailWord_385443).sum := by decide
  have hdescent : baseEnd_385443 < baseStart_385443 := by decide
  rcases family_descends (prefixWord ++ tailWord_385443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385635 : List Nat := [1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_385635 : Nat := 118140960795 + 385635 * 2 ^ 59
def prefixEnd_385635 : Nat := 4983230072969 + 3 ^ 40 * 385635 * 2
def baseEnd_385635 : Nat := 117342881301750479993483

theorem tailTrace_385635 : CollatzResearch.WordTrace tailWord_385635 prefixEnd_385635 117342881301750479993483 := by
  unfold tailWord_385635
  simp only [CollatzResearch.WordTrace]
  refine ⟨14065263957917731059630359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9376842638611820706420239 14065263957917731059630359)
  ·
    refine ⟨21097895936876596589445539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14065263957917731059630359 21097895936876596589445539)
    ·
      refine ⟨31646843905314894884168309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21097895936876596589445539 31646843905314894884168309)
      ·
        refine ⟨2966891616123271395390779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31646843905314894884168309 2966891616123271395390779)
        ·
          refine ⟨4450337424184907093086169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966891616123271395390779 4450337424184907093086169)
          ·
            refine ⟨3337753068138680319814627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4450337424184907093086169 3337753068138680319814627)
            ·
              refine ⟨5006629602208020479721941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337753068138680319814627 5006629602208020479721941)
              ·
                refine ⟨117342881301750479993483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5006629602208020479721941 117342881301750479993483)
                ·
                  rfl

theorem cell19_385635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_385635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385635 prefixEnd_385635 := by exact prefixLift 385635
  have htrace : WordTrace (prefixWord ++ tailWord_385635) baseStart_385635 baseEnd_385635 := by
    simpa [prefixWord, tailWord_385635, baseEnd_385635] using wordTrace_append hprefix tailTrace_385635
  have hstable : (prefixWord ++ tailWord_385635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385635).length < 2 ^ (prefixWord ++ tailWord_385635).sum := by decide
  have hdescent : baseEnd_385635 < baseStart_385635 := by decide
  rcases family_descends (prefixWord ++ tailWord_385635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385709 : List Nat := [1, 5, 2, 1, 1, 3, 6]
def baseStart_385709 : Nat := 118140960795 + 385709 * 2 ^ 59
def prefixEnd_385709 : Nat := 4983230072969 + 3 ^ 40 * 385709 * 2
def baseEnd_385709 : Nat := 39121799459780078116279

theorem tailTrace_385709 : CollatzResearch.WordTrace tailWord_385709 prefixEnd_385709 39121799459780078116279 := by
  unfold tailWord_385709
  simp only [CollatzResearch.WordTrace]
  refine ⟨14067962959649641697824181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9378641973099761131882787 14067962959649641697824181)
  ·
    refine ⟨1318871527467153909171017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14067962959649641697824181 1318871527467153909171017)
    ·
      refine ⟨989153645600365431878263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1318871527467153909171017 989153645600365431878263)
      ·
        refine ⟨1483730468400548147817395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989153645600365431878263 1483730468400548147817395)
        ·
          refine ⟨2225595702600822221726093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483730468400548147817395 2225595702600822221726093)
          ·
            refine ⟨834598388475308333147285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2225595702600822221726093 834598388475308333147285)
            ·
              refine ⟨39121799459780078116279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 834598388475308333147285 39121799459780078116279)
              ·
                rfl

theorem cell19_385709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 6].length) (baseStart_385709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385709 prefixEnd_385709 := by exact prefixLift 385709
  have htrace : WordTrace (prefixWord ++ tailWord_385709) baseStart_385709 baseEnd_385709 := by
    simpa [prefixWord, tailWord_385709, baseEnd_385709] using wordTrace_append hprefix tailTrace_385709
  have hstable : (prefixWord ++ tailWord_385709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385709).length < 2 ^ (prefixWord ++ tailWord_385709).sum := by decide
  have hdescent : baseEnd_385709 < baseStart_385709 := by decide
  rcases family_descends (prefixWord ++ tailWord_385709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385711 : List Nat := [1, 1, 2, 1, 2, 6, 6]
def baseStart_385711 : Nat := 118140960795 + 385711 * 2 ^ 59
def prefixEnd_385711 : Nat := 4983230072969 + 3 ^ 40 * 385711 * 2
def baseEnd_385711 : Nat := 39122002316334940768129

theorem tailTrace_385711 : CollatzResearch.WordTrace tailWord_385711 prefixEnd_385711 39122002316334940768129 := by
  unfold tailWord_385711
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068035905642396039396987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9378690603761597359597991 14068035905642396039396987)
  ·
    refine ⟨21102053858463594059095481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14068035905642396039396987 21102053858463594059095481)
    ·
      refine ⟨15826540393847695544321611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21102053858463594059095481 15826540393847695544321611)
      ·
        refine ⟨23739810590771543316482417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15826540393847695544321611 23739810590771543316482417)
        ·
          refine ⟨17804857943078657487361813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23739810590771543316482417 17804857943078657487361813)
          ·
            refine ⟨834602716081812069720085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17804857943078657487361813 834602716081812069720085)
            ·
              refine ⟨39122002316334940768129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 834602716081812069720085 39122002316334940768129)
              ·
                rfl

theorem cell19_385711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_385711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385711 prefixEnd_385711 := by exact prefixLift 385711
  have htrace : WordTrace (prefixWord ++ tailWord_385711) baseStart_385711 baseEnd_385711 := by
    simpa [prefixWord, tailWord_385711, baseEnd_385711] using wordTrace_append hprefix tailTrace_385711
  have hstable : (prefixWord ++ tailWord_385711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385711).length < 2 ^ (prefixWord ++ tailWord_385711).sum := by decide
  have hdescent : baseEnd_385711 < baseStart_385711 := by decide
  rcases family_descends (prefixWord ++ tailWord_385711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385741 : List Nat := [1, 6, 2, 1, 2, 2, 2, 3]
def baseStart_385741 : Nat := 118140960795 + 385741 * 2 ^ 59
def prefixEnd_385741 : Nat := 4983230072969 + 3 ^ 40 * 385741 * 2
def baseEnd_385741 : Nat := 117375135493973641637639

theorem tailTrace_385741 : CollatzResearch.WordTrace tailWord_385741 prefixEnd_385741 117375135493973641637639 := by
  unfold tailWord_385741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14069130095533711162989077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9379420063689140775326051 14069130095533711162989077)
  ·
    refine ⟨659490473228142710765113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14069130095533711162989077 659490473228142710765113)
    ·
      refine ⟨494617854921107033073835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 659490473228142710765113 494617854921107033073835)
      ·
        refine ⟨741926782381660549610753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 494617854921107033073835 741926782381660549610753)
        ·
          refine ⟨556445086786245412208065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 741926782381660549610753 556445086786245412208065)
          ·
            refine ⟨417333815089684059156049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 556445086786245412208065 417333815089684059156049)
            ·
              refine ⟨313000361317263044367037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417333815089684059156049 313000361317263044367037)
              ·
                refine ⟨117375135493973641637639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313000361317263044367037 117375135493973641637639)
                ·
                  rfl

theorem cell19_385741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_385741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385741 prefixEnd_385741 := by exact prefixLift 385741
  have htrace : WordTrace (prefixWord ++ tailWord_385741) baseStart_385741 baseEnd_385741 := by
    simpa [prefixWord, tailWord_385741, baseEnd_385741] using wordTrace_append hprefix tailTrace_385741
  have hstable : (prefixWord ++ tailWord_385741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385741).length < 2 ^ (prefixWord ++ tailWord_385741).sum := by decide
  have hdescent : baseEnd_385741 < baseStart_385741 := by decide
  rcases family_descends (prefixWord ++ tailWord_385741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385821 : List Nat := [1, 4, 2, 4, 2, 6]
def baseStart_385821 : Nat := 118140960795 + 385821 * 2 ^ 59
def prefixEnd_385821 : Nat := 4983230072969 + 3 ^ 40 * 385821 * 2
def baseEnd_385821 : Nat := 13044386475617462206627

theorem tailTrace_385821 : CollatzResearch.WordTrace tailWord_385821 prefixEnd_385821 13044386475617462206627 := by
  unfold tailWord_385821
  simp only [CollatzResearch.WordTrace]
  refine ⟨14072047935243884825901317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9381365290162589883934211 14072047935243884825901317)
  ·
    refine ⟨2638508987858228404856497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14072047935243884825901317 2638508987858228404856497)
    ·
      refine ⟨1978881740893671303642373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2638508987858228404856497 1978881740893671303642373)
      ·
        refine ⟨371040326417563369432945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1978881740893671303642373 371040326417563369432945)
        ·
          refine ⟨278280244813172527074709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371040326417563369432945 278280244813172527074709)
          ·
            refine ⟨13044386475617462206627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278280244813172527074709 13044386475617462206627)
            ·
              rfl

theorem cell19_385821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 6].length) (baseStart_385821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385821 prefixEnd_385821 := by exact prefixLift 385821
  have htrace : WordTrace (prefixWord ++ tailWord_385821) baseStart_385821 baseEnd_385821 := by
    simpa [prefixWord, tailWord_385821, baseEnd_385821] using wordTrace_append hprefix tailTrace_385821
  have hstable : (prefixWord ++ tailWord_385821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385821).length < 2 ^ (prefixWord ++ tailWord_385821).sum := by decide
  have hdescent : baseEnd_385821 < baseStart_385821 := by decide
  rcases family_descends (prefixWord ++ tailWord_385821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385857 : List Nat := [1, 2, 5, 3, 1, 1, 3, 3]
def baseStart_385857 : Nat := 118140960795 + 385857 * 2 ^ 59
def prefixEnd_385857 : Nat := 4983230072969 + 3 ^ 40 * 385857 * 2
def baseEnd_385857 : Nat := 117410432534519743059545

theorem tailTrace_385857 : CollatzResearch.WordTrace tailWord_385857 prefixEnd_385857 117410432534519743059545 := by
  unfold tailWord_385857
  simp only [CollatzResearch.WordTrace]
  refine ⟨14073360963113462974211825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9382240642075641982807883 14073360963113462974211825)
  ·
    refine ⟨10555020722335097230658869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14073360963113462974211825 10555020722335097230658869)
    ·
      refine ⟨989533192718915365374269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10555020722335097230658869 989533192718915365374269)
      ·
        refine ⟨371074947269593262015351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 989533192718915365374269 371074947269593262015351)
        ·
          refine ⟨556612420904389893023027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371074947269593262015351 556612420904389893023027)
          ·
            refine ⟨834918631356584839534541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556612420904389893023027 834918631356584839534541)
            ·
              refine ⟨313094486758719314825453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 834918631356584839534541 313094486758719314825453)
              ·
                refine ⟨117410432534519743059545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313094486758719314825453 117410432534519743059545)
                ·
                  rfl

theorem cell19_385857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3, 3].length) (baseStart_385857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385857 prefixEnd_385857 := by exact prefixLift 385857
  have htrace : WordTrace (prefixWord ++ tailWord_385857) baseStart_385857 baseEnd_385857 := by
    simpa [prefixWord, tailWord_385857, baseEnd_385857] using wordTrace_append hprefix tailTrace_385857
  have hstable : (prefixWord ++ tailWord_385857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385857).length < 2 ^ (prefixWord ++ tailWord_385857).sum := by decide
  have hdescent : baseEnd_385857 < baseStart_385857 := by decide
  rcases family_descends (prefixWord ++ tailWord_385857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385882 : List Nat := [3, 1, 1, 2, 1, 5, 6]
def baseStart_385882 : Nat := 118140960795 + 385882 * 2 ^ 59
def prefixEnd_385882 : Nat := 4983230072969 + 3 ^ 40 * 385882 * 2
def baseEnd_385882 : Nat := 39139346551775697501307

theorem tailTrace_385882 : CollatzResearch.WordTrace tailWord_385882 prefixEnd_385882 39139346551775697501307 := by
  unfold tailWord_385882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3518568197005723060967975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9382848525348594829247933 3518568197005723060967975)
  ·
    refine ⟨5277852295508584591451963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3518568197005723060967975 5277852295508584591451963)
    ·
      refine ⟨7916778443262876887177945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5277852295508584591451963 7916778443262876887177945)
      ·
        refine ⟨5937583832447157665383459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7916778443262876887177945 5937583832447157665383459)
        ·
          refine ⟨8906375748670736498075189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5937583832447157665383459 8906375748670736498075189)
          ·
            refine ⟨834972726437881546694549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8906375748670736498075189 834972726437881546694549)
            ·
              refine ⟨39139346551775697501307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 834972726437881546694549 39139346551775697501307)
              ·
                rfl

theorem cell19_385882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_385882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385882 prefixEnd_385882 := by exact prefixLift 385882
  have htrace : WordTrace (prefixWord ++ tailWord_385882) baseStart_385882 baseEnd_385882 := by
    simpa [prefixWord, tailWord_385882, baseEnd_385882] using wordTrace_append hprefix tailTrace_385882
  have hstable : (prefixWord ++ tailWord_385882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385882).length < 2 ^ (prefixWord ++ tailWord_385882).sum := by decide
  have hdescent : baseEnd_385882 < baseStart_385882 := by decide
  rcases family_descends (prefixWord ++ tailWord_385882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385901 : List Nat := [1, 5, 1, 1, 1, 1, 1, 8]
def baseStart_385901 : Nat := 118140960795 + 385901 * 2 ^ 59
def prefixEnd_385901 : Nat := 4983230072969 + 3 ^ 40 * 385901 * 2
def baseEnd_385901 : Nat := 117423821067140678081647

theorem tailTrace_385901 : CollatzResearch.WordTrace tailWord_385901 prefixEnd_385901 117423821067140678081647 := by
  unfold tailWord_385901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14074965774954058488813557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9383310516636038992542371 14074965774954058488813557)
  ·
    refine ⟨1319528041401942983326271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14074965774954058488813557 1319528041401942983326271)
    ·
      refine ⟨1979292062102914474989407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1319528041401942983326271 1979292062102914474989407)
      ·
        refine ⟨2968938093154371712484111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979292062102914474989407 2968938093154371712484111)
        ·
          refine ⟨4453407139731557568726167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2968938093154371712484111 4453407139731557568726167)
          ·
            refine ⟨6680110709597336353089251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453407139731557568726167 6680110709597336353089251)
            ·
              refine ⟨10020166064396004529633877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680110709597336353089251 10020166064396004529633877)
              ·
                refine ⟨117423821067140678081647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10020166064396004529633877 117423821067140678081647)
                ·
                  rfl

theorem cell19_385901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_385901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385901 prefixEnd_385901 := by exact prefixLift 385901
  have htrace : WordTrace (prefixWord ++ tailWord_385901) baseStart_385901 baseEnd_385901 := by
    simpa [prefixWord, tailWord_385901, baseEnd_385901] using wordTrace_append hprefix tailTrace_385901
  have hstable : (prefixWord ++ tailWord_385901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385901).length < 2 ^ (prefixWord ++ tailWord_385901).sum := by decide
  have hdescent : baseEnd_385901 < baseStart_385901 := by decide
  rcases family_descends (prefixWord ++ tailWord_385901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385977 : List Nat := [1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_385977 : Nat := 118140960795 + 385977 * 2 ^ 59
def prefixEnd_385977 : Nat := 4983230072969 + 3 ^ 40 * 385977 * 2
def baseEnd_385977 : Nat := 117446946714395020392551

theorem tailTrace_385977 : CollatzResearch.WordTrace tailWord_385977 prefixEnd_385977 117446946714395020392551 := by
  unfold tailWord_385977
  simp only [CollatzResearch.WordTrace]
  refine ⟨14077737722678723468580185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9385158481785815645720123 14077737722678723468580185)
  ·
    refine ⟨10558303292009042601435139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14077737722678723468580185 10558303292009042601435139)
    ·
      refine ⟨15837454938013563902152709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10558303292009042601435139 15837454938013563902152709)
      ·
        refine ⟨2969522800877543231653633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15837454938013563902152709 2969522800877543231653633)
        ·
          refine ⟨2227142100658157423740225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2969522800877543231653633 2227142100658157423740225)
          ·
            refine ⟨1670356575493618067805169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2227142100658157423740225 1670356575493618067805169)
            ·
              refine ⟨1252767431620213550853877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670356575493618067805169 1252767431620213550853877)
              ·
                refine ⟨117446946714395020392551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1252767431620213550853877 117446946714395020392551)
                ·
                  rfl

theorem cell19_385977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_385977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385977 prefixEnd_385977 := by exact prefixLift 385977
  have htrace : WordTrace (prefixWord ++ tailWord_385977) baseStart_385977 baseEnd_385977 := by
    simpa [prefixWord, tailWord_385977, baseEnd_385977] using wordTrace_append hprefix tailTrace_385977
  have hstable : (prefixWord ++ tailWord_385977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385977).length < 2 ^ (prefixWord ++ tailWord_385977).sum := by decide
  have hdescent : baseEnd_385977 < baseStart_385977 := by decide
  rcases family_descends (prefixWord ++ tailWord_385977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_385990 : List Nat := [6, 1, 3, 1, 8]
def baseStart_385990 : Nat := 118140960795 + 385990 * 2 ^ 59
def prefixEnd_385990 : Nat := 4983230072969 + 3 ^ 40 * 385990 * 2
def baseEnd_385990 : Nat := 4350033422859808966801

theorem tailTrace_385990 : CollatzResearch.WordTrace tailWord_385990 prefixEnd_385990 4350033422859808966801 := by
  unfold tailWord_385990
  simp only [CollatzResearch.WordTrace]
  refine ⟨439944120988488334025107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9385474581087751125868949 439944120988488334025107)
  ·
    refine ⟨659916181482732501037661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 439944120988488334025107 659916181482732501037661)
    ·
      refine ⟨247468568056024687889123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 659916181482732501037661 247468568056024687889123)
      ·
        refine ⟨371202852084037031833685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247468568056024687889123 371202852084037031833685)
        ·
          refine ⟨4350033422859808966801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 371202852084037031833685 4350033422859808966801)
          ·
            rfl

theorem cell19_385990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 8].length) (baseStart_385990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_385990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_385990 prefixEnd_385990 := by exact prefixLift 385990
  have htrace : WordTrace (prefixWord ++ tailWord_385990) baseStart_385990 baseEnd_385990 := by
    simpa [prefixWord, tailWord_385990, baseEnd_385990] using wordTrace_append hprefix tailTrace_385990
  have hstable : (prefixWord ++ tailWord_385990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_385990).length < 2 ^ (prefixWord ++ tailWord_385990).sum := by decide
  have hdescent : baseEnd_385990 < baseStart_385990 := by decide
  rcases family_descends (prefixWord ++ tailWord_385990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386013 : List Nat := [1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_386013 : Nat := 118140960795 + 386013 * 2 ^ 59
def prefixEnd_386013 : Nat := 4983230072969 + 3 ^ 40 * 386013 * 2
def baseEnd_386013 : Nat := 117457900968357603592453

theorem tailTrace_386013 : CollatzResearch.WordTrace tailWord_386013 prefixEnd_386013 117457900968357603592453 := by
  unfold tailWord_386013
  simp only [CollatzResearch.WordTrace]
  refine ⟨14079050750548301616890693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9386033833698867744593795 14079050750548301616890693)
  ·
    refine ⟨2639822015727806553167005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14079050750548301616890693 2639822015727806553167005)
    ·
      refine ⟨989933255897927457437627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2639822015727806553167005 989933255897927457437627)
      ·
        refine ⟨1484899883846891186156441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989933255897927457437627 1484899883846891186156441)
        ·
          refine ⟨1113674912885168389617331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1484899883846891186156441 1113674912885168389617331)
          ·
            refine ⟨1670512369327752584425997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113674912885168389617331 1670512369327752584425997)
            ·
              refine ⟨626442138497907219159749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1670512369327752584425997 626442138497907219159749)
              ·
                refine ⟨117457900968357603592453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 626442138497907219159749 117457900968357603592453)
                ·
                  rfl

theorem cell19_386013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_386013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386013 prefixEnd_386013 := by exact prefixLift 386013
  have htrace : WordTrace (prefixWord ++ tailWord_386013) baseStart_386013 baseEnd_386013 := by
    simpa [prefixWord, tailWord_386013, baseEnd_386013] using wordTrace_append hprefix tailTrace_386013
  have hstable : (prefixWord ++ tailWord_386013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386013).length < 2 ^ (prefixWord ++ tailWord_386013).sum := by decide
  have hdescent : baseEnd_386013 < baseStart_386013 := by decide
  rcases family_descends (prefixWord ++ tailWord_386013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386030 : List Nat := [4, 1, 2, 1, 4, 1, 3, 3]
def baseStart_386030 : Nat := 118140960795 + 386030 * 2 ^ 59
def prefixEnd_386030 : Nat := 4983230072969 + 3 ^ 40 * 386030 * 2
def baseEnd_386030 : Nat := 117463073810506601214629

theorem tailTrace_386030 : CollatzResearch.WordTrace tailWord_386030 prefixEnd_386030 117463073810506601214629 := by
  unfold tailWord_386030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1759958848935839190032443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9386447194324475680173029 1759958848935839190032443)
  ·
    refine ⟨2639938273403758785048665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1759958848935839190032443 2639938273403758785048665)
    ·
      refine ⟨1979953705052819088786499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2639938273403758785048665 1979953705052819088786499)
      ·
        refine ⟨2969930557579228633179749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979953705052819088786499 2969930557579228633179749)
        ·
          refine ⟨556861979546105368721203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2969930557579228633179749 556861979546105368721203)
          ·
            refine ⟨835292969319158053081805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556861979546105368721203 835292969319158053081805)
            ·
              refine ⟨313234863494684269905677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 835292969319158053081805 313234863494684269905677)
              ·
                refine ⟨117463073810506601214629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313234863494684269905677 117463073810506601214629)
                ·
                  rfl

theorem cell19_386030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_386030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386030 prefixEnd_386030 := by exact prefixLift 386030
  have htrace : WordTrace (prefixWord ++ tailWord_386030) baseStart_386030 baseEnd_386030 := by
    simpa [prefixWord, tailWord_386030, baseEnd_386030] using wordTrace_append hprefix tailTrace_386030
  have hstable : (prefixWord ++ tailWord_386030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386030).length < 2 ^ (prefixWord ++ tailWord_386030).sum := by decide
  have hdescent : baseEnd_386030 < baseStart_386030 := by decide
  rcases family_descends (prefixWord ++ tailWord_386030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386087 : List Nat := [1, 1, 7, 1, 1, 1, 4, 3]
def baseStart_386087 : Nat := 118140960795 + 386087 * 2 ^ 59
def prefixEnd_386087 : Nat := 4983230072969 + 3 ^ 40 * 386087 * 2
def baseEnd_386087 : Nat := 117480418045947357947807

theorem tailTrace_386087 : CollatzResearch.WordTrace tailWord_386087 prefixEnd_386087 117480418045947357947807 := by
  unfold tailWord_386087
  simp only [CollatzResearch.WordTrace]
  refine ⟨14081749752280212255084515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9387833168186808170056343 14081749752280212255084515)
  ·
    refine ⟨21122624628420318382626773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14081749752280212255084515 21122624628420318382626773)
    ·
      refine ⟨495061514728601212092815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 21122624628420318382626773 495061514728601212092815)
      ·
        refine ⟨742592272092901818139223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495061514728601212092815 742592272092901818139223)
        ·
          refine ⟨1113888408139352727208835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742592272092901818139223 1113888408139352727208835)
          ·
            refine ⟨1670832612209029090813253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113888408139352727208835 1670832612209029090813253)
            ·
              refine ⟨313281114789192954527485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1670832612209029090813253 313281114789192954527485)
              ·
                refine ⟨117480418045947357947807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313281114789192954527485 117480418045947357947807)
                ·
                  rfl

theorem cell19_386087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_386087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386087 prefixEnd_386087 := by exact prefixLift 386087
  have htrace : WordTrace (prefixWord ++ tailWord_386087) baseStart_386087 baseEnd_386087 := by
    simpa [prefixWord, tailWord_386087, baseEnd_386087] using wordTrace_append hprefix tailTrace_386087
  have hstable : (prefixWord ++ tailWord_386087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386087).length < 2 ^ (prefixWord ++ tailWord_386087).sum := by decide
  have hdescent : baseEnd_386087 < baseStart_386087 := by decide
  rcases family_descends (prefixWord ++ tailWord_386087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386131 : List Nat := [1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_386131 : Nat := 118140960795 + 386131 * 2 ^ 59
def prefixEnd_386131 : Nat := 4983230072969 + 3 ^ 40 * 386131 * 2
def baseEnd_386131 : Nat := 117493806578568292969909

theorem tailTrace_386131 : CollatzResearch.WordTrace tailWord_386131 prefixEnd_386131 117493806578568292969909 := by
  unfold tailWord_386131
  simp only [CollatzResearch.WordTrace]
  refine ⟨14083354564120807769686247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9388903042747205179790831 14083354564120807769686247)
  ·
    refine ⟨21125031846181211654529371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14083354564120807769686247 21125031846181211654529371)
    ·
      refine ⟨31687547769271817481794057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21125031846181211654529371 31687547769271817481794057)
      ·
        refine ⟨23765660826953863111345543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31687547769271817481794057 23765660826953863111345543)
        ·
          refine ⟨35648491240430794667018315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23765660826953863111345543 35648491240430794667018315)
          ·
            refine ⟨53472736860646192000527473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35648491240430794667018315 53472736860646192000527473)
            ·
              refine ⟨40104552645484644000395605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53472736860646192000527473 40104552645484644000395605)
              ·
                refine ⟨117493806578568292969909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40104552645484644000395605 117493806578568292969909)
                ·
                  rfl

theorem cell19_386131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_386131 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386131 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386131 prefixEnd_386131 := by exact prefixLift 386131
  have htrace : WordTrace (prefixWord ++ tailWord_386131) baseStart_386131 baseEnd_386131 := by
    simpa [prefixWord, tailWord_386131, baseEnd_386131] using wordTrace_append hprefix tailTrace_386131
  have hstable : (prefixWord ++ tailWord_386131).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386131).length < 2 ^ (prefixWord ++ tailWord_386131).sum := by decide
  have hdescent : baseEnd_386131 < baseStart_386131 := by decide
  rcases family_descends (prefixWord ++ tailWord_386131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386146 : List Nat := [3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_386146 : Nat := 118140960795 + 386146 * 2 ^ 59
def prefixEnd_386146 : Nat := 4983230072969 + 3 ^ 40 * 386146 * 2
def baseEnd_386146 : Nat := 117498370851052702636535

theorem tailTrace_386146 : CollatzResearch.WordTrace tailWord_386146 prefixEnd_386146 117498370851052702636535 := by
  unfold tailWord_386146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520975414766616332870573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9389267772710976887654861 3520975414766616332870573)
  ·
    refine ⟨1320365780537481124826465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3520975414766616332870573 1320365780537481124826465)
    ·
      refine ⟨990274335403110843619849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1320365780537481124826465 990274335403110843619849)
      ·
        refine ⟨742705751552333132714887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 990274335403110843619849 742705751552333132714887)
        ·
          refine ⟨1114058627328499699072331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 742705751552333132714887 1114058627328499699072331)
          ·
            refine ⟨1671087940992749548608497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114058627328499699072331 1671087940992749548608497)
            ·
              refine ⟨1253315955744562161456373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1671087940992749548608497 1253315955744562161456373)
              ·
                refine ⟨117498370851052702636535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1253315955744562161456373 117498370851052702636535)
                ·
                  rfl

theorem cell19_386146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_386146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386146 prefixEnd_386146 := by exact prefixLift 386146
  have htrace : WordTrace (prefixWord ++ tailWord_386146) baseStart_386146 baseEnd_386146 := by
    simpa [prefixWord, tailWord_386146, baseEnd_386146] using wordTrace_append hprefix tailTrace_386146
  have hstable : (prefixWord ++ tailWord_386146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386146).length < 2 ^ (prefixWord ++ tailWord_386146).sum := by decide
  have hdescent : baseEnd_386146 < baseStart_386146 := by decide
  rcases family_descends (prefixWord ++ tailWord_386146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386165 : List Nat := [1, 3, 4, 3, 1, 7]
def baseStart_386165 : Nat := 118140960795 + 386165 * 2 ^ 59
def prefixEnd_386165 : Nat := 4983230072969 + 3 ^ 40 * 386165 * 2
def baseEnd_386165 : Nat := 13056016918096254246029

theorem tailTrace_386165 : CollatzResearch.WordTrace tailWord_386165 prefixEnd_386165 13056016918096254246029 := by
  unfold tailWord_386165
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084594645997631576423949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9389729763998421050949299 14084594645997631576423949)
  ·
    refine ⟨5281722992249111841158981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14084594645997631576423949 5281722992249111841158981)
    ·
      refine ⟨990323061046708470217309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5281722992249111841158981 990323061046708470217309)
      ·
        refine ⟨371371147892515676331491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 990323061046708470217309 371371147892515676331491)
        ·
          refine ⟨557056721838773514497237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371371147892515676331491 557056721838773514497237)
          ·
            refine ⟨13056016918096254246029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 557056721838773514497237 13056016918096254246029)
            ·
              rfl

theorem cell19_386165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 7].length) (baseStart_386165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386165 prefixEnd_386165 := by exact prefixLift 386165
  have htrace : WordTrace (prefixWord ++ tailWord_386165) baseStart_386165 baseEnd_386165 := by
    simpa [prefixWord, tailWord_386165, baseEnd_386165] using wordTrace_append hprefix tailTrace_386165
  have hstable : (prefixWord ++ tailWord_386165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386165).length < 2 ^ (prefixWord ++ tailWord_386165).sum := by decide
  have hdescent : baseEnd_386165 < baseStart_386165 := by decide
  rcases family_descends (prefixWord ++ tailWord_386165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386169 : List Nat := [1, 2, 1, 3, 12]
def baseStart_386169 : Nat := 118140960795 + 386169 * 2 ^ 59
def prefixEnd_386169 : Nat := 4983230072969 + 3 ^ 40 * 386169 * 2
def baseEnd_386169 : Nat := 4352050718599832004643

theorem tailTrace_386169 : CollatzResearch.WordTrace tailWord_386169 prefixEnd_386169 4352050718599832004643 := by
  unfold tailWord_386169
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084740537983140259569561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9389827025322093506379707 14084740537983140259569561)
  ·
    refine ⟨10563555403487355194677171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14084740537983140259569561 10563555403487355194677171)
    ·
      refine ⟨15845333105231032792015757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10563555403487355194677171 15845333105231032792015757)
      ·
        refine ⟨5941999914461637297005909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15845333105231032792015757 5941999914461637297005909)
        ·
          refine ⟨4352050718599832004643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5941999914461637297005909 4352050718599832004643)
          ·
            rfl

theorem cell19_386169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 12].length) (baseStart_386169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386169 prefixEnd_386169 := by exact prefixLift 386169
  have htrace : WordTrace (prefixWord ++ tailWord_386169) baseStart_386169 baseEnd_386169 := by
    simpa [prefixWord, tailWord_386169, baseEnd_386169] using wordTrace_append hprefix tailTrace_386169
  have hstable : (prefixWord ++ tailWord_386169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386169).length < 2 ^ (prefixWord ++ tailWord_386169).sum := by decide
  have hdescent : baseEnd_386169 < baseStart_386169 := by decide
  rcases family_descends (prefixWord ++ tailWord_386169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386245 : List Nat := [1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_386245 : Nat := 118140960795 + 386245 * 2 ^ 59
def prefixEnd_386245 : Nat := 4983230072969 + 3 ^ 40 * 386245 * 2
def baseEnd_386245 : Nat := 117528495049449806436265

theorem tailTrace_386245 : CollatzResearch.WordTrace tailWord_386245 prefixEnd_386245 117528495049449806436265 := by
  unfold tailWord_386245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14087512485707805239336189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9391674990471870159557459 14087512485707805239336189)
  ·
    refine ⟨5282817182140426964751071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14087512485707805239336189 5282817182140426964751071)
    ·
      refine ⟨7924225773210640447126607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5282817182140426964751071 7924225773210640447126607)
      ·
        refine ⟨11886338659815960670689911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7924225773210640447126607 11886338659815960670689911)
        ·
          refine ⟨17829507989723941006034867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11886338659815960670689911 17829507989723941006034867)
          ·
            refine ⟨26744261984585911509052301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17829507989723941006034867 26744261984585911509052301)
            ·
              refine ⟨10029098244219716815894613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26744261984585911509052301 10029098244219716815894613)
              ·
                refine ⟨117528495049449806436265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10029098244219716815894613 117528495049449806436265)
                ·
                  rfl

theorem cell19_386245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_386245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386245 prefixEnd_386245 := by exact prefixLift 386245
  have htrace : WordTrace (prefixWord ++ tailWord_386245) baseStart_386245 baseEnd_386245 := by
    simpa [prefixWord, tailWord_386245, baseEnd_386245] using wordTrace_append hprefix tailTrace_386245
  have hstable : (prefixWord ++ tailWord_386245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386245).length < 2 ^ (prefixWord ++ tailWord_386245).sum := by decide
  have hdescent : baseEnd_386245 < baseStart_386245 := by decide
  rcases family_descends (prefixWord ++ tailWord_386245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386279 : List Nat := [1, 1, 5, 3, 2, 2, 5]
def baseStart_386279 : Nat := 118140960795 + 386279 * 2 ^ 59
def prefixEnd_386279 : Nat := 4983230072969 + 3 ^ 40 * 386279 * 2
def baseEnd_386279 : Nat := 39179613577915933893539

theorem tailTrace_386279 : CollatzResearch.WordTrace tailWord_386279 prefixEnd_386279 39179613577915933893539 := by
  unfold tailWord_386279
  simp only [CollatzResearch.WordTrace]
  refine ⟨14088752567584629046073891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9392501711723086030715927 14088752567584629046073891)
  ·
    refine ⟨21133128851376943569110837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14088752567584629046073891 21133128851376943569110837)
    ·
      refine ⟨1981230829816588459604141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21133128851376943569110837 1981230829816588459604141)
      ·
        refine ⟨742961561181220672351553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1981230829816588459604141 742961561181220672351553)
        ·
          refine ⟨557221170885915504263665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742961561181220672351553 557221170885915504263665)
          ·
            refine ⟨417915878164436628197749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557221170885915504263665 417915878164436628197749)
            ·
              refine ⟨39179613577915933893539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 417915878164436628197749 39179613577915933893539)
              ·
                rfl

theorem cell19_386279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 5].length) (baseStart_386279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386279 prefixEnd_386279 := by exact prefixLift 386279
  have htrace : WordTrace (prefixWord ++ tailWord_386279) baseStart_386279 baseEnd_386279 := by
    simpa [prefixWord, tailWord_386279, baseEnd_386279] using wordTrace_append hprefix tailTrace_386279
  have hstable : (prefixWord ++ tailWord_386279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386279).length < 2 ^ (prefixWord ++ tailWord_386279).sum := by decide
  have hdescent : baseEnd_386279 < baseStart_386279 := by decide
  rcases family_descends (prefixWord ++ tailWord_386279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386283 : List Nat := [1, 1, 1, 1, 2, 6, 7]
def baseStart_386283 : Nat := 118140960795 + 386283 * 2 ^ 59
def prefixEnd_386283 : Nat := 4983230072969 + 3 ^ 40 * 386283 * 2
def baseEnd_386283 : Nat := 39180019291025659197239

theorem tailTrace_386283 : CollatzResearch.WordTrace tailWord_386283 prefixEnd_386283 39180019291025659197239 := by
  unfold tailWord_386283
  simp only [CollatzResearch.WordTrace]
  refine ⟨14088898459570137729219503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9392598973046758486146335 14088898459570137729219503)
  ·
    refine ⟨21133347689355206593829255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14088898459570137729219503 21133347689355206593829255)
    ·
      refine ⟨31700021534032809890743883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21133347689355206593829255 31700021534032809890743883)
      ·
        refine ⟨47550032301049214836115825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31700021534032809890743883 47550032301049214836115825)
        ·
          refine ⟨35662524225786911127086869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47550032301049214836115825 35662524225786911127086869)
          ·
            refine ⟨1671680823083761459082197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35662524225786911127086869 1671680823083761459082197)
            ·
              refine ⟨39180019291025659197239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1671680823083761459082197 39180019291025659197239)
              ·
                rfl

theorem cell19_386283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_386283 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386283 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386283 prefixEnd_386283 := by exact prefixLift 386283
  have htrace : WordTrace (prefixWord ++ tailWord_386283) baseStart_386283 baseEnd_386283 := by
    simpa [prefixWord, tailWord_386283, baseEnd_386283] using wordTrace_append hprefix tailTrace_386283
  have hstable : (prefixWord ++ tailWord_386283).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386283).length < 2 ^ (prefixWord ++ tailWord_386283).sum := by decide
  have hdescent : baseEnd_386283 < baseStart_386283 := by decide
  rcases family_descends (prefixWord ++ tailWord_386283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386321 : List Nat := [1, 2, 2, 1, 1, 4, 1, 7]
def baseStart_386321 : Nat := 118140960795 + 386321 * 2 ^ 59
def prefixEnd_386321 : Nat := 4983230072969 + 3 ^ 40 * 386321 * 2
def baseEnd_386321 : Nat := 117551620696704148747169

theorem tailTrace_386321 : CollatzResearch.WordTrace tailWord_386321 prefixEnd_386321 117551620696704148747169 := by
  unfold tailWord_386321
  simp only [CollatzResearch.WordTrace]
  refine ⟨14090284433432470219102817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9393522955621646812735211 14090284433432470219102817)
  ·
    refine ⟨10567713325074352664327113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14090284433432470219102817 10567713325074352664327113)
    ·
      refine ⟨7925784993805764498245335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10567713325074352664327113 7925784993805764498245335)
      ·
        refine ⟨11888677490708646747368003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925784993805764498245335 11888677490708646747368003)
        ·
          refine ⟨17833016236062970121052005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11888677490708646747368003 17833016236062970121052005)
          ·
            refine ⟨3343690544261806897697251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17833016236062970121052005 3343690544261806897697251)
            ·
              refine ⟨5015535816392710346545877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3343690544261806897697251 5015535816392710346545877)
              ·
                refine ⟨117551620696704148747169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5015535816392710346545877 117551620696704148747169)
                ·
                  rfl

theorem cell19_386321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_386321 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386321 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386321 prefixEnd_386321 := by exact prefixLift 386321
  have htrace : WordTrace (prefixWord ++ tailWord_386321) baseStart_386321 baseEnd_386321 := by
    simpa [prefixWord, tailWord_386321, baseEnd_386321] using wordTrace_append hprefix tailTrace_386321
  have hstable : (prefixWord ++ tailWord_386321).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386321).length < 2 ^ (prefixWord ++ tailWord_386321).sum := by decide
  have hdescent : baseEnd_386321 < baseStart_386321 := by decide
  rcases family_descends (prefixWord ++ tailWord_386321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386334 : List Nat := [4, 3, 2, 1, 3, 6]
def baseStart_386334 : Nat := 118140960795 + 386334 * 2 ^ 59
def prefixEnd_386334 : Nat := 4983230072969 + 3 ^ 40 * 386334 * 2
def baseEnd_386334 : Nat := 13061730711058218939805

theorem tailTrace_386334 : CollatzResearch.WordTrace tailWord_386334 prefixEnd_386334 13061730711058218939805 := by
  unfold tailWord_386334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1761344822798171679915757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9393839054923582292884037 1761344822798171679915757)
  ·
    refine ⟨660504308549314379968409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1761344822798171679915757 660504308549314379968409)
    ·
      refine ⟨495378231411985784976307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660504308549314379968409 495378231411985784976307)
      ·
        refine ⟨743067347117978677464461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495378231411985784976307 743067347117978677464461)
        ·
          refine ⟨278650255169242004049173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 743067347117978677464461 278650255169242004049173)
          ·
            refine ⟨13061730711058218939805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278650255169242004049173 13061730711058218939805)
            ·
              rfl

theorem cell19_386334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 6].length) (baseStart_386334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386334 prefixEnd_386334 := by exact prefixLift 386334
  have htrace : WordTrace (prefixWord ++ tailWord_386334) baseStart_386334 baseEnd_386334 := by
    simpa [prefixWord, tailWord_386334, baseEnd_386334] using wordTrace_append hprefix tailTrace_386334
  have hstable : (prefixWord ++ tailWord_386334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386334).length < 2 ^ (prefixWord ++ tailWord_386334).sum := by decide
  have hdescent : baseEnd_386334 < baseStart_386334 := by decide
  rcases family_descends (prefixWord ++ tailWord_386334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386338 : List Nat := [3, 3, 1, 1, 4, 7]
def baseStart_386338 : Nat := 118140960795 + 386338 * 2 ^ 59
def prefixEnd_386338 : Nat := 4983230072969 + 3 ^ 40 * 386338 * 2
def baseEnd_386338 : Nat := 13061865948761460707705

theorem tailTrace_386338 : CollatzResearch.WordTrace tailWord_386338 prefixEnd_386338 13061865948761460707705 := by
  unfold tailWord_386338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3522726118592720530617917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9393936316247254748314445 3522726118592720530617917)
  ·
    refine ⟨1321022294472270198981719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3522726118592720530617917 1321022294472270198981719)
    ·
      refine ⟨1981533441708405298472579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1321022294472270198981719 1981533441708405298472579)
      ·
        refine ⟨2972300162562607947708869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981533441708405298472579 2972300162562607947708869)
        ·
          refine ⟨557306280480488990195413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2972300162562607947708869 557306280480488990195413)
          ·
            refine ⟨13061865948761460707705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 557306280480488990195413 13061865948761460707705)
            ·
              rfl

theorem cell19_386338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_386338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386338 prefixEnd_386338 := by exact prefixLift 386338
  have htrace : WordTrace (prefixWord ++ tailWord_386338) baseStart_386338 baseEnd_386338 := by
    simpa [prefixWord, tailWord_386338, baseEnd_386338] using wordTrace_append hprefix tailTrace_386338
  have hstable : (prefixWord ++ tailWord_386338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386338).length < 2 ^ (prefixWord ++ tailWord_386338).sum := by decide
  have hdescent : baseEnd_386338 < baseStart_386338 := by decide
  rcases family_descends (prefixWord ++ tailWord_386338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386357 : List Nat := [1, 3, 3, 1, 2, 2, 3, 4]
def baseStart_386357 : Nat := 118140960795 + 386357 * 2 ^ 59
def prefixEnd_386357 : Nat := 4983230072969 + 3 ^ 40 * 386357 * 2
def baseEnd_386357 : Nat := 117562574950666731947071

theorem tailTrace_386357 : CollatzResearch.WordTrace tailWord_386357 prefixEnd_386357 117562574950666731947071 := by
  unfold tailWord_386357
  simp only [CollatzResearch.WordTrace]
  refine ⟨14091597461302048367413325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9394398307534698911608883 14091597461302048367413325)
  ·
    refine ⟨5284349047988268137779997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14091597461302048367413325 5284349047988268137779997)
    ·
      refine ⟨1981630892995600551667499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5284349047988268137779997 1981630892995600551667499)
      ·
        refine ⟨2972446339493400827501249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1981630892995600551667499 2972446339493400827501249)
        ·
          refine ⟨2229334754620050620625937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2972446339493400827501249 2229334754620050620625937)
          ·
            refine ⟨1672001065965037965469453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2229334754620050620625937 1672001065965037965469453)
            ·
              refine ⟨627000399736889237051045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1672001065965037965469453 627000399736889237051045)
              ·
                refine ⟨117562574950666731947071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627000399736889237051045 117562574950666731947071)
                ·
                  rfl

theorem cell19_386357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_386357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386357 prefixEnd_386357 := by exact prefixLift 386357
  have htrace : WordTrace (prefixWord ++ tailWord_386357) baseStart_386357 baseEnd_386357 := by
    simpa [prefixWord, tailWord_386357, baseEnd_386357] using wordTrace_append hprefix tailTrace_386357
  have hstable : (prefixWord ++ tailWord_386357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386357).length < 2 ^ (prefixWord ++ tailWord_386357).sum := by decide
  have hdescent : baseEnd_386357 < baseStart_386357 := by decide
  rcases family_descends (prefixWord ++ tailWord_386357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386372 : List Nat := [2, 3, 4, 1, 1, 2, 3, 3]
def baseStart_386372 : Nat := 118140960795 + 386372 * 2 ^ 59
def prefixEnd_386372 : Nat := 4983230072969 + 3 ^ 40 * 386372 * 2
def baseEnd_386372 : Nat := 117567139223151141613697

theorem tailTrace_386372 : CollatzResearch.WordTrace tailWord_386372 prefixEnd_386372 117567139223151141613697 := by
  unfold tailWord_386372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046072278123852964604685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9394763037498470619472913 7046072278123852964604685)
  ·
    refine ⟨2642277104296444861726757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7046072278123852964604685 2642277104296444861726757)
    ·
      refine ⟨495426957055583411573767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2642277104296444861726757 495426957055583411573767)
      ·
        refine ⟨743140435583375117360651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495426957055583411573767 743140435583375117360651)
        ·
          refine ⟨1114710653375062676040977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743140435583375117360651 1114710653375062676040977)
          ·
            refine ⟨836032990031297007030733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1114710653375062676040977 836032990031297007030733)
            ·
              refine ⟨313512371261736377636525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836032990031297007030733 313512371261736377636525)
              ·
                refine ⟨117567139223151141613697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313512371261736377636525 117567139223151141613697)
                ·
                  rfl

theorem cell19_386372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 3].length) (baseStart_386372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386372 prefixEnd_386372 := by exact prefixLift 386372
  have htrace : WordTrace (prefixWord ++ tailWord_386372) baseStart_386372 baseEnd_386372 := by
    simpa [prefixWord, tailWord_386372, baseEnd_386372] using wordTrace_append hprefix tailTrace_386372
  have hstable : (prefixWord ++ tailWord_386372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386372).length < 2 ^ (prefixWord ++ tailWord_386372).sum := by decide
  have hdescent : baseEnd_386372 < baseStart_386372 := by decide
  rcases family_descends (prefixWord ++ tailWord_386372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386378 : List Nat := [3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_386378 : Nat := 118140960795 + 386378 * 2 ^ 59
def prefixEnd_386378 : Nat := 4983230072969 + 3 ^ 40 * 386378 * 2
def baseEnd_386378 : Nat := 117568964932144905480347

theorem tailTrace_386378 : CollatzResearch.WordTrace tailWord_386378 prefixEnd_386378 117568964932144905480347 := by
  unfold tailWord_386378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3523090848556492238481947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9394908929483979302618525 3523090848556492238481947)
  ·
    refine ⟨5284636272834738357722921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3523090848556492238481947 5284636272834738357722921)
    ·
      refine ⟨3963477204626053768292191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5284636272834738357722921 3963477204626053768292191)
      ·
        refine ⟨5945215806939080652438287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963477204626053768292191 5945215806939080652438287)
        ·
          refine ⟨8917823710408620978657431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945215806939080652438287 8917823710408620978657431)
          ·
            refine ⟨13376735565612931467986147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917823710408620978657431 13376735565612931467986147)
            ·
              refine ⟨20065103348419397201979221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13376735565612931467986147 20065103348419397201979221)
              ·
                refine ⟨117568964932144905480347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20065103348419397201979221 117568964932144905480347)
                ·
                  rfl

theorem cell19_386378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_386378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386378 prefixEnd_386378 := by exact prefixLift 386378
  have htrace : WordTrace (prefixWord ++ tailWord_386378) baseStart_386378 baseEnd_386378 := by
    simpa [prefixWord, tailWord_386378, baseEnd_386378] using wordTrace_append hprefix tailTrace_386378
  have hstable : (prefixWord ++ tailWord_386378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386378).length < 2 ^ (prefixWord ++ tailWord_386378).sum := by decide
  have hdescent : baseEnd_386378 < baseStart_386378 := by decide
  rcases family_descends (prefixWord ++ tailWord_386378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386416 : List Nat := [2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_386416 : Nat := 118140960795 + 386416 * 2 ^ 59
def prefixEnd_386416 : Nat := 4983230072969 + 3 ^ 40 * 386416 * 2
def baseEnd_386416 : Nat := 117580527755772076635799

theorem tailTrace_386416 : CollatzResearch.WordTrace tailWord_386416 prefixEnd_386416 117580527755772076635799 := by
  unfold tailWord_386416
  simp only [CollatzResearch.WordTrace]
  refine ⟨7046874684044150721905551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9395832912058867629207401 7046874684044150721905551)
  ·
    refine ⟨10570312026066226082858327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7046874684044150721905551 10570312026066226082858327)
    ·
      refine ⟨15855468039099339124287491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10570312026066226082858327 15855468039099339124287491)
      ·
        refine ⟨23783202058649008686431237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15855468039099339124287491 23783202058649008686431237)
        ·
          refine ⟨4459350385996689128705857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23783202058649008686431237 4459350385996689128705857)
          ·
            refine ⟨3344512789497516846529393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4459350385996689128705857 3344512789497516846529393)
            ·
              refine ⟨2508384592123137634897045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344512789497516846529393 2508384592123137634897045)
              ·
                refine ⟨117580527755772076635799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2508384592123137634897045 117580527755772076635799)
                ·
                  rfl

theorem cell19_386416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_386416 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386416 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386416 prefixEnd_386416 := by exact prefixLift 386416
  have htrace : WordTrace (prefixWord ++ tailWord_386416) baseStart_386416 baseEnd_386416 := by
    simpa [prefixWord, tailWord_386416, baseEnd_386416] using wordTrace_append hprefix tailTrace_386416
  have hstable : (prefixWord ++ tailWord_386416).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386416).length < 2 ^ (prefixWord ++ tailWord_386416).sum := by decide
  have hdescent : baseEnd_386416 < baseStart_386416 := by decide
  rcases family_descends (prefixWord ++ tailWord_386416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386452 : List Nat := [2, 4, 2, 1, 2, 1, 7]
def baseStart_386452 : Nat := 118140960795 + 386452 * 2 ^ 59
def prefixEnd_386452 : Nat := 4983230072969 + 3 ^ 40 * 386452 * 2
def baseEnd_386452 : Nat := 39197160669911553278567

theorem tailTrace_386452 : CollatzResearch.WordTrace tailWord_386452 prefixEnd_386452 39197160669911553278567 := by
  unfold tailWord_386452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047531197978939796060805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9396708263971919728081073 7047531197978939796060805)
  ·
    refine ⟨1321412099621051211761401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7047531197978939796060805 1321412099621051211761401)
    ·
      refine ⟨991059074715788408821051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1321412099621051211761401 991059074715788408821051)
      ·
        refine ⟨1486588612073682613231577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991059074715788408821051 1486588612073682613231577)
        ·
          refine ⟨1114941459055261959923683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1486588612073682613231577 1114941459055261959923683)
          ·
            refine ⟨1672412188582892939885525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114941459055261959923683 1672412188582892939885525)
            ·
              refine ⟨39197160669911553278567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1672412188582892939885525 39197160669911553278567)
              ·
                rfl

theorem cell19_386452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_386452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386452 prefixEnd_386452 := by exact prefixLift 386452
  have htrace : WordTrace (prefixWord ++ tailWord_386452) baseStart_386452 baseEnd_386452 := by
    simpa [prefixWord, tailWord_386452, baseEnd_386452] using wordTrace_append hprefix tailTrace_386452
  have hstable : (prefixWord ++ tailWord_386452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386452).length < 2 ^ (prefixWord ++ tailWord_386452).sum := by decide
  have hdescent : baseEnd_386452 < baseStart_386452 := by decide
  rcases family_descends (prefixWord ++ tailWord_386452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386471 : List Nat := [1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_386471 : Nat := 118140960795 + 386471 * 2 ^ 59
def prefixEnd_386471 : Nat := 4983230072969 + 3 ^ 40 * 386471 * 2
def baseEnd_386471 : Nat := 117597263421548245413427

theorem tailTrace_386471 : CollatzResearch.WordTrace tailWord_386471 prefixEnd_386471 117597263421548245413427 := by
  unfold tailWord_386471
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095755382889045837063267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9397170255259363891375511 14095755382889045837063267)
  ·
    refine ⟨21143633074333568755594901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14095755382889045837063267 21143633074333568755594901)
    ·
      refine ⟨991107800359386035418511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21143633074333568755594901 991107800359386035418511)
      ·
        refine ⟨1486661700539079053127767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991107800359386035418511 1486661700539079053127767)
        ·
          refine ⟨2229992550808618579691651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1486661700539079053127767 2229992550808618579691651)
          ·
            refine ⟨3344988826212927869537477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2229992550808618579691651 3344988826212927869537477)
            ·
              refine ⟨627185404914923975538277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3344988826212927869537477 627185404914923975538277)
              ·
                refine ⟨117597263421548245413427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627185404914923975538277 117597263421548245413427)
                ·
                  rfl

theorem cell19_386471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_386471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386471 prefixEnd_386471 := by exact prefixLift 386471
  have htrace : WordTrace (prefixWord ++ tailWord_386471) baseStart_386471 baseEnd_386471 := by
    simpa [prefixWord, tailWord_386471, baseEnd_386471] using wordTrace_append hprefix tailTrace_386471
  have hstable : (prefixWord ++ tailWord_386471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386471).length < 2 ^ (prefixWord ++ tailWord_386471).sum := by decide
  have hdescent : baseEnd_386471 < baseStart_386471 := by decide
  rcases family_descends (prefixWord ++ tailWord_386471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386600 : List Nat := [2, 1, 5, 2, 2, 2, 2, 3]
def baseStart_386600 : Nat := 118140960795 + 386600 * 2 ^ 59
def prefixEnd_386600 : Nat := 4983230072969 + 3 ^ 40 * 386600 * 2
def baseEnd_386600 : Nat := 117636516164914168546409

theorem tailTrace_386600 : CollatzResearch.WordTrace tailWord_386600 prefixEnd_386600 117636516164914168546409 := by
  unfold tailWord_386600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050230199710850434254627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9400306932947800579006169 7050230199710850434254627)
  ·
    refine ⟨10575345299566275651381941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7050230199710850434254627 10575345299566275651381941)
    ·
      refine ⟨991438621834338342317057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10575345299566275651381941 991438621834338342317057)
      ·
        refine ⟨743578966375753756737793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 991438621834338342317057 743578966375753756737793)
        ·
          refine ⟨557684224781815317553345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743578966375753756737793 557684224781815317553345)
          ·
            refine ⟨418263168586361488165009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557684224781815317553345 418263168586361488165009)
            ·
              refine ⟨313697376439771116123757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418263168586361488165009 313697376439771116123757)
              ·
                refine ⟨117636516164914168546409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313697376439771116123757 117636516164914168546409)
                ·
                  rfl

theorem cell19_386600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_386600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386600 prefixEnd_386600 := by exact prefixLift 386600
  have htrace : WordTrace (prefixWord ++ tailWord_386600) baseStart_386600 baseEnd_386600 := by
    simpa [prefixWord, tailWord_386600, baseEnd_386600] using wordTrace_append hprefix tailTrace_386600
  have hstable : (prefixWord ++ tailWord_386600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386600).length < 2 ^ (prefixWord ++ tailWord_386600).sum := by decide
  have hdescent : baseEnd_386600 < baseStart_386600 := by decide
  rcases family_descends (prefixWord ++ tailWord_386600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386621 : List Nat := [1, 4, 1, 3, 4, 1, 5]
def baseStart_386621 : Nat := 118140960795 + 386621 * 2 ^ 59
def prefixEnd_386621 : Nat := 4983230072969 + 3 ^ 40 * 386621 * 2
def baseEnd_386621 : Nat := 39214302048797447359895

theorem tailTrace_386621 : CollatzResearch.WordTrace tailWord_386621 prefixEnd_386621 39214302048797447359895 := by
  unfold tailWord_386621
  simp only [CollatzResearch.WordTrace]
  refine ⟨14101226332345621455023717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9400817554897080970015811 14101226332345621455023717)
  ·
    refine ⟨2643979937314804022816947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14101226332345621455023717 2643979937314804022816947)
    ·
      refine ⟨3965969905972206034225421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2643979937314804022816947 3965969905972206034225421)
      ·
        refine ⟨1487238714739577262834533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3965969905972206034225421 1487238714739577262834533)
        ·
          refine ⟨278857259013670736781475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1487238714739577262834533 278857259013670736781475)
          ·
            refine ⟨418285888520506105172213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278857259013670736781475 418285888520506105172213)
            ·
              refine ⟨39214302048797447359895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 418285888520506105172213 39214302048797447359895)
              ·
                rfl

theorem cell19_386621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_386621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386621 prefixEnd_386621 := by exact prefixLift 386621
  have htrace : WordTrace (prefixWord ++ tailWord_386621) baseStart_386621 baseEnd_386621 := by
    simpa [prefixWord, tailWord_386621, baseEnd_386621] using wordTrace_append hprefix tailTrace_386621
  have hstable : (prefixWord ++ tailWord_386621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386621).length < 2 ^ (prefixWord ++ tailWord_386621).sum := by decide
  have hdescent : baseEnd_386621 < baseStart_386621 := by decide
  rcases family_descends (prefixWord ++ tailWord_386621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386642 : List Nat := [3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_386642 : Nat := 118140960795 + 386642 * 2 ^ 59
def prefixEnd_386642 : Nat := 4983230072969 + 3 ^ 40 * 386642 * 2
def baseEnd_386642 : Nat := 117649296127870515612961

theorem tailTrace_386642 : CollatzResearch.WordTrace tailWord_386642 prefixEnd_386642 117649296127870515612961 := by
  unfold tailWord_386642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525498066317385510384545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9401328176846361361025453 3525498066317385510384545)
  ·
    refine ⟨2644123549738039132788409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3525498066317385510384545 2644123549738039132788409)
    ·
      refine ⟨1983092662303529349591307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2644123549738039132788409 1983092662303529349591307)
      ·
        refine ⟨2974638993455294024386961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983092662303529349591307 2974638993455294024386961)
        ·
          refine ⟨2230979245091470518290221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2974638993455294024386961 2230979245091470518290221)
          ·
            refine ⟨836617216909301444358833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2230979245091470518290221 836617216909301444358833)
            ·
              refine ⟨627462912681976083269125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836617216909301444358833 627462912681976083269125)
              ·
                refine ⟨117649296127870515612961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627462912681976083269125 117649296127870515612961)
                ·
                  rfl

theorem cell19_386642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_386642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386642 prefixEnd_386642 := by exact prefixLift 386642
  have htrace : WordTrace (prefixWord ++ tailWord_386642) baseStart_386642 baseEnd_386642 := by
    simpa [prefixWord, tailWord_386642, baseEnd_386642] using wordTrace_append hprefix tailTrace_386642
  have hstable : (prefixWord ++ tailWord_386642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386642).length < 2 ^ (prefixWord ++ tailWord_386642).sum := by decide
  have hdescent : baseEnd_386642 < baseStart_386642 := by decide
  rcases family_descends (prefixWord ++ tailWord_386642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386663 : List Nat := [1, 1, 5, 1, 1, 1, 4, 5]
def baseStart_386663 : Nat := 118140960795 + 386663 * 2 ^ 59
def prefixEnd_386663 : Nat := 4983230072969 + 3 ^ 40 * 386663 * 2
def baseEnd_386663 : Nat := 117655686109348689146237

theorem tailTrace_386663 : CollatzResearch.WordTrace tailWord_386663 prefixEnd_386663 117655686109348689146237 := by
  unfold tailWord_386663
  simp only [CollatzResearch.WordTrace]
  refine ⟨14102758198193462628052643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9401838798795641752035095 14102758198193462628052643)
  ·
    refine ⟨21154137297290193942078965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14102758198193462628052643 21154137297290193942078965)
    ·
      refine ⟨1983200371620955682069903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21154137297290193942078965 1983200371620955682069903)
      ·
        refine ⟨2974800557431433523104855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983200371620955682069903 2974800557431433523104855)
        ·
          refine ⟨4462200836147150284657283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974800557431433523104855 4462200836147150284657283)
          ·
            refine ⟨6693301254220725426985925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462200836147150284657283 6693301254220725426985925)
            ·
              refine ⟨1254993985166386017559861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6693301254220725426985925 1254993985166386017559861)
              ·
                refine ⟨117655686109348689146237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1254993985166386017559861 117655686109348689146237)
                ·
                  rfl

theorem cell19_386663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_386663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386663 prefixEnd_386663 := by exact prefixLift 386663
  have htrace : WordTrace (prefixWord ++ tailWord_386663) baseStart_386663 baseEnd_386663 := by
    simpa [prefixWord, tailWord_386663, baseEnd_386663] using wordTrace_append hprefix tailTrace_386663
  have hstable : (prefixWord ++ tailWord_386663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386663).length < 2 ^ (prefixWord ++ tailWord_386663).sum := by decide
  have hdescent : baseEnd_386663 < baseStart_386663 := by decide
  rcases family_descends (prefixWord ++ tailWord_386663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386716 : List Nat := [2, 2, 3, 2, 3, 1, 3, 3]
def baseStart_386716 : Nat := 118140960795 + 386716 * 2 ^ 59
def prefixEnd_386716 : Nat := 4983230072969 + 3 ^ 40 * 386716 * 2
def baseEnd_386716 : Nat := 117671813205460269968315

theorem tailTrace_386716 : CollatzResearch.WordTrace tailWord_386716 prefixEnd_386716 117671813205460269968315 := by
  unfold tailWord_386716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052345633500726339866001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9403127511334301786488001 7052345633500726339866001)
  ·
    refine ⟨5289259225125544754899501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7052345633500726339866001 5289259225125544754899501)
    ·
      refine ⟨1983472209422079283087313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5289259225125544754899501 1983472209422079283087313)
      ·
        refine ⟨1487604157066559462315485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1983472209422079283087313 1487604157066559462315485)
        ·
          refine ⟨557851558899959798368307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1487604157066559462315485 557851558899959798368307)
          ·
            refine ⟨836777338349939697552461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557851558899959798368307 836777338349939697552461)
            ·
              refine ⟨313791501881227386582173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836777338349939697552461 313791501881227386582173)
              ·
                refine ⟨117671813205460269968315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313791501881227386582173 117671813205460269968315)
                ·
                  rfl

theorem cell19_386716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_386716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386716 prefixEnd_386716 := by exact prefixLift 386716
  have htrace : WordTrace (prefixWord ++ tailWord_386716) baseStart_386716 baseEnd_386716 := by
    simpa [prefixWord, tailWord_386716, baseEnd_386716] using wordTrace_append hprefix tailTrace_386716
  have hstable : (prefixWord ++ tailWord_386716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386716).length < 2 ^ (prefixWord ++ tailWord_386716).sum := by decide
  have hdescent : baseEnd_386716 < baseStart_386716 := by decide
  rcases family_descends (prefixWord ++ tailWord_386716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386777 : List Nat := [1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_386777 : Nat := 118140960795 + 386777 * 2 ^ 59
def prefixEnd_386777 : Nat := 4983230072969 + 3 ^ 40 * 386777 * 2
def baseEnd_386777 : Nat := 117690374580230202612593

theorem tailTrace_386777 : CollatzResearch.WordTrace tailWord_386777 prefixEnd_386777 117690374580230202612593 := by
  unfold tailWord_386777
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106916119780460097702585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9404610746520306731801723 14106916119780460097702585)
  ·
    refine ⟨10580187089835345073276939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14106916119780460097702585 10580187089835345073276939)
    ·
      refine ⟨15870280634753017609915409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10580187089835345073276939 15870280634753017609915409)
      ·
        refine ⟨11902710476064763207436557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15870280634753017609915409 11902710476064763207436557)
        ·
          refine ⟨4463516428524286202788709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11902710476064763207436557 4463516428524286202788709)
          ·
            refine ⟨836909330348303663022883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4463516428524286202788709 836909330348303663022883)
            ·
              refine ⟨1255363995522455494534325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836909330348303663022883 1255363995522455494534325)
              ·
                refine ⟨117690374580230202612593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1255363995522455494534325 117690374580230202612593)
                ·
                  rfl

theorem cell19_386777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_386777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386777 prefixEnd_386777 := by exact prefixLift 386777
  have htrace : WordTrace (prefixWord ++ tailWord_386777) baseStart_386777 baseEnd_386777 := by
    simpa [prefixWord, tailWord_386777, baseEnd_386777] using wordTrace_append hprefix tailTrace_386777
  have hstable : (prefixWord ++ tailWord_386777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386777).length < 2 ^ (prefixWord ++ tailWord_386777).sum := by decide
  have hdescent : baseEnd_386777 < baseStart_386777 := by decide
  rcases family_descends (prefixWord ++ tailWord_386777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386855 : List Nat := [1, 1, 17]
def baseStart_386855 : Nat := 118140960795 + 386855 * 2 ^ 59
def prefixEnd_386855 : Nat := 4983230072969 + 3 ^ 40 * 386855 * 2
def baseEnd_386855 : Nat := 484420200811313304029

theorem tailTrace_386855 : CollatzResearch.WordTrace tailWord_386855 prefixEnd_386855 484420200811313304029 := by
  unfold tailWord_386855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109761013497879419042019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9406507342331919612694679 14109761013497879419042019)
  ·
    refine ⟨21164641520246819128563029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14109761013497879419042019 21164641520246819128563029)
    ·
      refine ⟨484420200811313304029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 21164641520246819128563029 484420200811313304029)
      ·
        rfl

theorem cell19_386855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 17].length) (baseStart_386855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386855 prefixEnd_386855 := by exact prefixLift 386855
  have htrace : WordTrace (prefixWord ++ tailWord_386855) baseStart_386855 baseEnd_386855 := by
    simpa [prefixWord, tailWord_386855, baseEnd_386855] using wordTrace_append hprefix tailTrace_386855
  have hstable : (prefixWord ++ tailWord_386855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386855).length < 2 ^ (prefixWord ++ tailWord_386855).sum := by decide
  have hdescent : baseEnd_386855 < baseStart_386855 := by decide
  rcases family_descends (prefixWord ++ tailWord_386855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386868 : List Nat := [2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_386868 : Nat := 118140960795 + 386868 * 2 ^ 59
def prefixEnd_386868 : Nat := 4983230072969 + 3 ^ 40 * 386868 * 2
def baseEnd_386868 : Nat := 117718064499968954590123

theorem tailTrace_386868 : CollatzResearch.WordTrace tailWord_386868 prefixEnd_386868 117718064499968954590123 := by
  unfold tailWord_386868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7055117581225391319632629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9406823441633855092843505 7055117581225391319632629)
  ·
    refine ⟨661417273239880436215559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7055117581225391319632629 661417273239880436215559)
    ·
      refine ⟨992125909859820654323339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661417273239880436215559 992125909859820654323339)
      ·
        refine ⟨1488188864789730981485009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 992125909859820654323339 1488188864789730981485009)
        ·
          refine ⟨1116141648592298236113757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1488188864789730981485009 1116141648592298236113757)
          ·
            refine ⟨418553118222111838542659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1116141648592298236113757 418553118222111838542659)
            ·
              refine ⟨627829677333167757813989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418553118222111838542659 627829677333167757813989)
              ·
                refine ⟨117718064499968954590123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627829677333167757813989 117718064499968954590123)
                ·
                  rfl

theorem cell19_386868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_386868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386868 prefixEnd_386868 := by exact prefixLift 386868
  have htrace : WordTrace (prefixWord ++ tailWord_386868) baseStart_386868 baseEnd_386868 := by
    simpa [prefixWord, tailWord_386868, baseEnd_386868] using wordTrace_append hprefix tailTrace_386868
  have hstable : (prefixWord ++ tailWord_386868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386868).length < 2 ^ (prefixWord ++ tailWord_386868).sum := by decide
  have hdescent : baseEnd_386868 < baseStart_386868 := by decide
  rcases family_descends (prefixWord ++ tailWord_386868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386872 : List Nat := [2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_386872 : Nat := 118140960795 + 386872 * 2 ^ 59
def prefixEnd_386872 : Nat := 4983230072969 + 3 ^ 40 * 386872 * 2
def baseEnd_386872 : Nat := 117719281639298130501223

theorem tailTrace_386872 : CollatzResearch.WordTrace tailWord_386872 prefixEnd_386872 117719281639298130501223 := by
  unfold tailWord_386872
  simp only [CollatzResearch.WordTrace]
  refine ⟨7055190527218145661205435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9406920702957527548273913 7055190527218145661205435)
  ·
    refine ⟨10582785790827218491808153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7055190527218145661205435 10582785790827218491808153)
    ·
      refine ⟨7937089343120413868856115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10582785790827218491808153 7937089343120413868856115)
      ·
        refine ⟨11905634014680620803284173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7937089343120413868856115 11905634014680620803284173)
        ·
          refine ⟨4464612755505232801231565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11905634014680620803284173 4464612755505232801231565)
          ·
            refine ⟨1674229783314462300461837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4464612755505232801231565 1674229783314462300461837)
            ·
              refine ⟨627836168742923362673189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1674229783314462300461837 627836168742923362673189)
              ·
                refine ⟨117719281639298130501223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627836168742923362673189 117719281639298130501223)
                ·
                  rfl

theorem cell19_386872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_386872 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386872 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386872 prefixEnd_386872 := by exact prefixLift 386872
  have htrace : WordTrace (prefixWord ++ tailWord_386872) baseStart_386872 baseEnd_386872 := by
    simpa [prefixWord, tailWord_386872, baseEnd_386872] using wordTrace_append hprefix tailTrace_386872
  have hstable : (prefixWord ++ tailWord_386872).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386872).length < 2 ^ (prefixWord ++ tailWord_386872).sum := by decide
  have hdescent : baseEnd_386872 < baseStart_386872 := by decide
  rcases family_descends (prefixWord ++ tailWord_386872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386908 : List Nat := [2, 2, 4, 2, 2, 1, 6]
def baseStart_386908 : Nat := 118140960795 + 386908 * 2 ^ 59
def prefixEnd_386908 : Nat := 4983230072969 + 3 ^ 40 * 386908 * 2
def baseEnd_386908 : Nat := 39243411964420237900375

theorem tailTrace_386908 : CollatzResearch.WordTrace tailWord_386908 prefixEnd_386908 39243411964420237900375 := by
  unfold tailWord_386908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7055847041152934735360689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9407796054870579647147585 7055847041152934735360689)
  ·
    refine ⟨5291885280864701051520517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7055847041152934735360689 5291885280864701051520517)
    ·
      refine ⟨992228490162131447160097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5291885280864701051520517 992228490162131447160097)
      ·
        refine ⟨744171367621598585370073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992228490162131447160097 744171367621598585370073)
        ·
          refine ⟨558128525716198939027555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 744171367621598585370073 558128525716198939027555)
          ·
            refine ⟨837192788574298408541333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 558128525716198939027555 837192788574298408541333)
            ·
              refine ⟨39243411964420237900375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 837192788574298408541333 39243411964420237900375)
              ·
                rfl

theorem cell19_386908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 6].length) (baseStart_386908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386908 prefixEnd_386908 := by exact prefixLift 386908
  have htrace : WordTrace (prefixWord ++ tailWord_386908) baseStart_386908 baseEnd_386908 := by
    simpa [prefixWord, tailWord_386908, baseEnd_386908] using wordTrace_append hprefix tailTrace_386908
  have hstable : (prefixWord ++ tailWord_386908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386908).length < 2 ^ (prefixWord ++ tailWord_386908).sum := by decide
  have hdescent : baseEnd_386908 < baseStart_386908 := by decide
  rcases family_descends (prefixWord ++ tailWord_386908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386931 : List Nat := [1, 1, 1, 2, 2, 1, 3, 8]
def baseStart_386931 : Nat := 118140960795 + 386931 * 2 ^ 59
def prefixEnd_386931 : Nat := 4983230072969 + 3 ^ 40 * 386931 * 2
def baseEnd_386931 : Nat := 117737234444403475189951

theorem tailTrace_386931 : CollatzResearch.WordTrace tailWord_386931 prefixEnd_386931 117737234444403475189951 := by
  unfold tailWord_386931
  simp only [CollatzResearch.WordTrace]
  refine ⟨14112532961222544398808647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9408355307481696265872431 14112532961222544398808647)
  ·
    refine ⟨21168799441833816598212971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14112532961222544398808647 21168799441833816598212971)
    ·
      refine ⟨31753199162750724897319457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21168799441833816598212971 31753199162750724897319457)
      ·
        refine ⟨23814899372063043672989593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31753199162750724897319457 23814899372063043672989593)
        ·
          refine ⟨17861174529047282754742195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23814899372063043672989593 17861174529047282754742195)
          ·
            refine ⟨26791761793570924132113293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17861174529047282754742195 26791761793570924132113293)
            ·
              refine ⟨10046910672589096549542485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26791761793570924132113293 10046910672589096549542485)
              ·
                refine ⟨117737234444403475189951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10046910672589096549542485 117737234444403475189951)
                ·
                  rfl

theorem cell19_386931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_386931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386931 prefixEnd_386931 := by exact prefixLift 386931
  have htrace : WordTrace (prefixWord ++ tailWord_386931) baseStart_386931 baseEnd_386931 := by
    simpa [prefixWord, tailWord_386931, baseEnd_386931] using wordTrace_append hprefix tailTrace_386931
  have hstable : (prefixWord ++ tailWord_386931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386931).length < 2 ^ (prefixWord ++ tailWord_386931).sum := by decide
  have hdescent : baseEnd_386931 < baseStart_386931 := by decide
  rcases family_descends (prefixWord ++ tailWord_386931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386942 : List Nat := [4, 2, 3, 1, 1, 3, 2, 3]
def baseStart_386942 : Nat := 118140960795 + 386942 * 2 ^ 59
def prefixEnd_386942 : Nat := 4983230072969 + 3 ^ 40 * 386942 * 2
def baseEnd_386942 : Nat := 117740581577558708945477

theorem tailTrace_386942 : CollatzResearch.WordTrace tailWord_386942 prefixEnd_386942 117740581577558708945477 := by
  unfold tailWord_386942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764116770522836659682385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9408622776121795518306053 1764116770522836659682385)
  ·
    refine ⟨1323087577892127494761789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1764116770522836659682385 1323087577892127494761789)
    ·
      refine ⟨496157841709547810535671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1323087577892127494761789 496157841709547810535671)
      ·
        refine ⟨744236762564321715803507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496157841709547810535671 744236762564321715803507)
        ·
          refine ⟨1116355143846482573705261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744236762564321715803507 1116355143846482573705261)
          ·
            refine ⟨418633178942430965139473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1116355143846482573705261 418633178942430965139473)
            ·
              refine ⟨313974884206823223854605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418633178942430965139473 313974884206823223854605)
              ·
                refine ⟨117740581577558708945477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313974884206823223854605 117740581577558708945477)
                ·
                  rfl

theorem cell19_386942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_386942 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386942 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386942 prefixEnd_386942 := by exact prefixLift 386942
  have htrace : WordTrace (prefixWord ++ tailWord_386942) baseStart_386942 baseEnd_386942 := by
    simpa [prefixWord, tailWord_386942, baseEnd_386942] using wordTrace_append hprefix tailTrace_386942
  have hstable : (prefixWord ++ tailWord_386942).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386942).length < 2 ^ (prefixWord ++ tailWord_386942).sum := by decide
  have hdescent : baseEnd_386942 < baseStart_386942 := by decide
  rcases family_descends (prefixWord ++ tailWord_386942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386967 : List Nat := [1, 1, 3, 3, 1, 5, 5]
def baseStart_386967 : Nat := 118140960795 + 386967 * 2 ^ 59
def prefixEnd_386967 : Nat := 4983230072969 + 3 ^ 40 * 386967 * 2
def baseEnd_386967 : Nat := 39249396232788686129951

theorem tailTrace_386967 : CollatzResearch.WordTrace tailWord_386967 prefixEnd_386967 39249396232788686129951 := by
  unfold tailWord_386967
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113845989092122547119155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9409230659394748364746103 14113845989092122547119155)
  ·
    refine ⟨21170768983638183820678733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14113845989092122547119155 21170768983638183820678733)
    ·
      refine ⟨7939038368864318932754525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21170768983638183820678733 7939038368864318932754525)
      ·
        refine ⟨2977139388324119599782947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7939038368864318932754525 2977139388324119599782947)
        ·
          refine ⟨4465709082486179399674421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2977139388324119599782947 4465709082486179399674421)
          ·
            refine ⟨418660226483079318719477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4465709082486179399674421 418660226483079318719477)
            ·
              refine ⟨39249396232788686129951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 418660226483079318719477 39249396232788686129951)
              ·
                rfl

theorem cell19_386967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_386967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386967 prefixEnd_386967 := by exact prefixLift 386967
  have htrace : WordTrace (prefixWord ++ tailWord_386967) baseStart_386967 baseEnd_386967 := by
    simpa [prefixWord, tailWord_386967, baseEnd_386967] using wordTrace_append hprefix tailTrace_386967
  have hstable : (prefixWord ++ tailWord_386967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386967).length < 2 ^ (prefixWord ++ tailWord_386967).sum := by decide
  have hdescent : baseEnd_386967 < baseStart_386967 := by decide
  rcases family_descends (prefixWord ++ tailWord_386967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_386969 : List Nat := [1, 2, 1, 2, 1, 3, 9]
def baseStart_386969 : Nat := 118140960795 + 386969 * 2 ^ 59
def prefixEnd_386969 : Nat := 4983230072969 + 3 ^ 40 * 386969 * 2
def baseEnd_386969 : Nat := 39249599089343548781801

theorem tailTrace_386969 : CollatzResearch.WordTrace tailWord_386969 prefixEnd_386969 39249599089343548781801 := by
  unfold tailWord_386969
  simp only [CollatzResearch.WordTrace]
  refine ⟨14113918935084876888691961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9409279290056584592461307 14113918935084876888691961)
  ·
    refine ⟨10585439201313657666518971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14113918935084876888691961 10585439201313657666518971)
    ·
      refine ⟨15878158801970486499778457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10585439201313657666518971 15878158801970486499778457)
      ·
        refine ⟨11908619101477864874833843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15878158801970486499778457 11908619101477864874833843)
        ·
          refine ⟨17862928652216797312250765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11908619101477864874833843 17862928652216797312250765)
          ·
            refine ⟨6698598244581298992094037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17862928652216797312250765 6698598244581298992094037)
            ·
              refine ⟨39249599089343548781801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6698598244581298992094037 39249599089343548781801)
              ·
                rfl

theorem cell19_386969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 9].length) (baseStart_386969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_386969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_386969 prefixEnd_386969 := by exact prefixLift 386969
  have htrace : WordTrace (prefixWord ++ tailWord_386969) baseStart_386969 baseEnd_386969 := by
    simpa [prefixWord, tailWord_386969, baseEnd_386969] using wordTrace_append hprefix tailTrace_386969
  have hstable : (prefixWord ++ tailWord_386969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_386969).length < 2 ^ (prefixWord ++ tailWord_386969).sum := by decide
  have hdescent : baseEnd_386969 < baseStart_386969 := by decide
  rcases family_descends (prefixWord ++ tailWord_386969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387005 : List Nat := [1, 4, 1, 2, 3, 1, 2, 5]
def baseStart_387005 : Nat := 118140960795 + 387005 * 2 ^ 59
def prefixEnd_387005 : Nat := 4983230072969 + 3 ^ 40 * 387005 * 2
def baseEnd_387005 : Nat := 117759751521993229545305

theorem tailTrace_387005 : CollatzResearch.WordTrace tailWord_387005 prefixEnd_387005 117759751521993229545305 := by
  unfold tailWord_387005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115231962954455037002469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9410154641969636691334979 14115231962954455037002469)
  ·
    refine ⟨2646605993053960319437963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14115231962954455037002469 2646605993053960319437963)
    ·
      refine ⟨3969908989580940479156945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2646605993053960319437963 3969908989580940479156945)
      ·
        refine ⟨2977431742185705359367709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3969908989580940479156945 2977431742185705359367709)
        ·
          refine ⟨1116536903319639509762891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2977431742185705359367709 1116536903319639509762891)
          ·
            refine ⟨1674805354979459264644337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116536903319639509762891 1674805354979459264644337)
            ·
              refine ⟨1256104016234594448483253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674805354979459264644337 1256104016234594448483253)
              ·
                refine ⟨117759751521993229545305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1256104016234594448483253 117759751521993229545305)
                ·
                  rfl

theorem cell19_387005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_387005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387005 prefixEnd_387005 := by exact prefixLift 387005
  have htrace : WordTrace (prefixWord ++ tailWord_387005) baseStart_387005 baseEnd_387005 := by
    simpa [prefixWord, tailWord_387005, baseEnd_387005] using wordTrace_append hprefix tailTrace_387005
  have hstable : (prefixWord ++ tailWord_387005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387005).length < 2 ^ (prefixWord ++ tailWord_387005).sum := by decide
  have hdescent : baseEnd_387005 < baseStart_387005 := by decide
  rcases family_descends (prefixWord ++ tailWord_387005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387007 : List Nat := [1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_387007 : Nat := 118140960795 + 387007 * 2 ^ 59
def prefixEnd_387007 : Nat := 4983230072969 + 3 ^ 40 * 387007 * 2
def baseEnd_387007 : Nat := 117760360091657817500855

theorem tailTrace_387007 : CollatzResearch.WordTrace tailWord_387007 prefixEnd_387007 117760360091657817500855 := by
  unfold tailWord_387007
  simp only [CollatzResearch.WordTrace]
  refine ⟨14115304908947209378575275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9410203272631472919050183 14115304908947209378575275)
  ·
    refine ⟨21172957363420814067862913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14115304908947209378575275 21172957363420814067862913)
    ·
      refine ⟨15879718022565610550897185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21172957363420814067862913 15879718022565610550897185)
      ·
        refine ⟨11909788516924207913172889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15879718022565610550897185 11909788516924207913172889)
        ·
          refine ⟨8932341387693155934879667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11909788516924207913172889 8932341387693155934879667)
          ·
            refine ⟨13398512081539733902319501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8932341387693155934879667 13398512081539733902319501)
            ·
              refine ⟨5024442030577400213369813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13398512081539733902319501 5024442030577400213369813)
              ·
                refine ⟨117760360091657817500855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5024442030577400213369813 117760360091657817500855)
                ·
                  rfl

theorem cell19_387007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_387007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387007 prefixEnd_387007 := by exact prefixLift 387007
  have htrace : WordTrace (prefixWord ++ tailWord_387007) baseStart_387007 baseEnd_387007 := by
    simpa [prefixWord, tailWord_387007, baseEnd_387007] using wordTrace_append hprefix tailTrace_387007
  have hstable : (prefixWord ++ tailWord_387007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387007).length < 2 ^ (prefixWord ++ tailWord_387007).sum := by decide
  have hdescent : baseEnd_387007 < baseStart_387007 := by decide
  rcases family_descends (prefixWord ++ tailWord_387007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387043 : List Nat := [1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_387043 : Nat := 118140960795 + 387043 * 2 ^ 59
def prefixEnd_387043 : Nat := 4983230072969 + 3 ^ 40 * 387043 * 2
def baseEnd_387043 : Nat := 117771314345620400700757

theorem tailTrace_387043 : CollatzResearch.WordTrace tailWord_387043 prefixEnd_387043 117771314345620400700757 := by
  unfold tailWord_387043
  simp only [CollatzResearch.WordTrace]
  refine ⟨14116617936816787526885783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9411078624544525017923855 14116617936816787526885783)
  ·
    refine ⟨21174926905225181290328675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14116617936816787526885783 21174926905225181290328675)
    ·
      refine ⟨31762390357837771935493013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21174926905225181290328675 31762390357837771935493013)
      ·
        refine ⟨1488862048023645559476235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31762390357837771935493013 1488862048023645559476235)
        ·
          refine ⟨2233293072035468339214353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1488862048023645559476235 2233293072035468339214353)
          ·
            refine ⟨1674969804026601254410765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2233293072035468339214353 1674969804026601254410765)
            ·
              refine ⟨628113676509975470404037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1674969804026601254410765 628113676509975470404037)
              ·
                refine ⟨117771314345620400700757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628113676509975470404037 117771314345620400700757)
                ·
                  rfl

theorem cell19_387043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_387043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387043 prefixEnd_387043 := by exact prefixLift 387043
  have htrace : WordTrace (prefixWord ++ tailWord_387043) baseStart_387043 baseEnd_387043 := by
    simpa [prefixWord, tailWord_387043, baseEnd_387043] using wordTrace_append hprefix tailTrace_387043
  have hstable : (prefixWord ++ tailWord_387043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387043).length < 2 ^ (prefixWord ++ tailWord_387043).sum := by decide
  have hdescent : baseEnd_387043 < baseStart_387043 := by decide
  rcases family_descends (prefixWord ++ tailWord_387043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387064 : List Nat := [2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_387064 : Nat := 118140960795 + 387064 * 2 ^ 59
def prefixEnd_387064 : Nat := 4983230072969 + 3 ^ 40 * 387064 * 2
def baseEnd_387064 : Nat := 117777704327098574234033

theorem tailTrace_387064 : CollatzResearch.WordTrace tailWord_387064 prefixEnd_387064 117777704327098574234033 := by
  unfold tailWord_387064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7058691934870354056700123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9411589246493805408933497 7058691934870354056700123)
  ·
    refine ⟨10588037902305531085050185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7058691934870354056700123 10588037902305531085050185)
    ·
      refine ⟨7941028426729148313787639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10588037902305531085050185 7941028426729148313787639)
      ·
        refine ⟨11911542640093722470681459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7941028426729148313787639 11911542640093722470681459)
        ·
          refine ⟨17867313960140583706022189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11911542640093722470681459 17867313960140583706022189)
          ·
            refine ⟨6700242735052718889758321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17867313960140583706022189 6700242735052718889758321)
            ·
              refine ⟨5025182051289539167318741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6700242735052718889758321 5025182051289539167318741)
              ·
                refine ⟨117777704327098574234033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5025182051289539167318741 117777704327098574234033)
                ·
                  rfl

theorem cell19_387064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_387064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387064 prefixEnd_387064 := by exact prefixLift 387064
  have htrace : WordTrace (prefixWord ++ tailWord_387064) baseStart_387064 baseEnd_387064 := by
    simpa [prefixWord, tailWord_387064, baseEnd_387064] using wordTrace_append hprefix tailTrace_387064
  have hstable : (prefixWord ++ tailWord_387064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387064).length < 2 ^ (prefixWord ++ tailWord_387064).sum := by decide
  have hdescent : baseEnd_387064 < baseStart_387064 := by decide
  rcases family_descends (prefixWord ++ tailWord_387064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387083 : List Nat := [1, 1, 1, 1, 6, 1, 8]
def baseStart_387083 : Nat := 118140960795 + 387083 * 2 ^ 59
def prefixEnd_387083 : Nat := 4983230072969 + 3 ^ 40 * 387083 * 2
def baseEnd_387083 : Nat := 39261161912970719937253

theorem tailTrace_387083 : CollatzResearch.WordTrace tailWord_387083 prefixEnd_387083 39261161912970719937253 := by
  unfold tailWord_387083
  simp only [CollatzResearch.WordTrace]
  refine ⟨14118076856671874358341903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9412051237781249572227935 14118076856671874358341903)
  ·
    refine ⟨21177115285007811537512855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14118076856671874358341903 21177115285007811537512855)
    ·
      refine ⟨31765672927511717306269283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21177115285007811537512855 31765672927511717306269283)
      ·
        refine ⟨47648509391267575959403925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31765672927511717306269283 47648509391267575959403925)
        ·
          refine ⟨2233523877715667623097059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 47648509391267575959403925 2233523877715667623097059)
          ·
            refine ⟨3350285816573501434645589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2233523877715667623097059 3350285816573501434645589)
            ·
              refine ⟨39261161912970719937253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3350285816573501434645589 39261161912970719937253)
              ·
                rfl

theorem cell19_387083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_387083 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387083 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387083 prefixEnd_387083 := by exact prefixLift 387083
  have htrace : WordTrace (prefixWord ++ tailWord_387083) baseStart_387083 baseEnd_387083 := by
    simpa [prefixWord, tailWord_387083, baseEnd_387083] using wordTrace_append hprefix tailTrace_387083
  have hstable : (prefixWord ++ tailWord_387083).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387083).length < 2 ^ (prefixWord ++ tailWord_387083).sum := by decide
  have hdescent : baseEnd_387083 < baseStart_387083 := by decide
  rcases family_descends (prefixWord ++ tailWord_387083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387134 : List Nat := [4, 2, 1, 3, 3, 1, 5]
def baseStart_387134 : Nat := 118140960795 + 387134 * 2 ^ 59
def prefixEnd_387134 : Nat := 4983230072969 + 3 ^ 40 * 387134 * 2
def baseEnd_387134 : Nat := 39266334755119717559429

theorem tailTrace_387134 : CollatzResearch.WordTrace tailWord_387134 prefixEnd_387134 39266334755119717559429 := by
  unfold tailWord_387134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764992122435888758556057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9413291319658073378965637 1764992122435888758556057)
  ·
    refine ⟨1323744091826916568917043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1764992122435888758556057 1323744091826916568917043)
    ·
      refine ⟨1985616137740374853375565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1323744091826916568917043 1985616137740374853375565)
      ·
        refine ⟨744606051652640570015837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1985616137740374853375565 744606051652640570015837)
        ·
          refine ⟨279227269369740213755939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 744606051652640570015837 279227269369740213755939)
          ·
            refine ⟨418840904054610320633909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279227269369740213755939 418840904054610320633909)
            ·
              refine ⟨39266334755119717559429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 418840904054610320633909 39266334755119717559429)
              ·
                rfl

theorem cell19_387134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_387134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387134 prefixEnd_387134 := by exact prefixLift 387134
  have htrace : WordTrace (prefixWord ++ tailWord_387134) baseStart_387134 baseEnd_387134 := by
    simpa [prefixWord, tailWord_387134, baseEnd_387134] using wordTrace_append hprefix tailTrace_387134
  have hstable : (prefixWord ++ tailWord_387134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387134).length < 2 ^ (prefixWord ++ tailWord_387134).sum := by decide
  have hdescent : baseEnd_387134 < baseStart_387134 := by decide
  rcases family_descends (prefixWord ++ tailWord_387134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387157 : List Nat := [1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_387157 : Nat := 118140960795 + 387157 * 2 ^ 59
def prefixEnd_387157 : Nat := 4983230072969 + 3 ^ 40 * 387157 * 2
def baseEnd_387157 : Nat := 117806002816501914167113

theorem tailTrace_387157 : CollatzResearch.WordTrace tailWord_387157 prefixEnd_387157 117806002816501914167113 := by
  unfold tailWord_387157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120775858403784996535725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9413850572269189997690483 14120775858403784996535725)
  ·
    refine ⟨5295290946901419373700897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14120775858403784996535725 5295290946901419373700897)
    ·
      refine ⟨3971468210176064530275673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5295290946901419373700897 3971468210176064530275673)
      ·
        refine ⟨2978601157632048397706755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3971468210176064530275673 2978601157632048397706755)
        ·
          refine ⟨4467901736448072596560133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2978601157632048397706755 4467901736448072596560133)
          ·
            refine ⟨837731575584013611855025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4467901736448072596560133 837731575584013611855025)
            ·
              refine ⟨628298681688010208891269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 837731575584013611855025 628298681688010208891269)
              ·
                refine ⟨117806002816501914167113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628298681688010208891269 117806002816501914167113)
                ·
                  rfl

theorem cell19_387157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_387157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387157 prefixEnd_387157 := by exact prefixLift 387157
  have htrace : WordTrace (prefixWord ++ tailWord_387157) baseStart_387157 baseEnd_387157 := by
    simpa [prefixWord, tailWord_387157, baseEnd_387157] using wordTrace_append hprefix tailTrace_387157
  have hstable : (prefixWord ++ tailWord_387157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387157).length < 2 ^ (prefixWord ++ tailWord_387157).sum := by decide
  have hdescent : baseEnd_387157 < baseStart_387157 := by decide
  rcases family_descends (prefixWord ++ tailWord_387157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387159 : List Nat := [1, 1, 3, 2, 2, 1, 3, 6]
def baseStart_387159 : Nat := 118140960795 + 387159 * 2 ^ 59
def prefixEnd_387159 : Nat := 4983230072969 + 3 ^ 40 * 387159 * 2
def baseEnd_387159 : Nat := 117806611386166502122663

theorem tailTrace_387159 : CollatzResearch.WordTrace tailWord_387159 prefixEnd_387159 117806611386166502122663 := by
  unfold tailWord_387159
  simp only [CollatzResearch.WordTrace]
  refine ⟨14120848804396539338108531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9413899202931026225405687 14120848804396539338108531)
  ·
    refine ⟨21181273206594809007162797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14120848804396539338108531 21181273206594809007162797)
    ·
      refine ⟨7942977452473053377686049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21181273206594809007162797 7942977452473053377686049)
      ·
        refine ⟨5957233089354790033264537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7942977452473053377686049 5957233089354790033264537)
        ·
          refine ⟨4467924817016092524948403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5957233089354790033264537 4467924817016092524948403)
          ·
            refine ⟨6701887225524138787422605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4467924817016092524948403 6701887225524138787422605)
            ·
              refine ⟨2513207709571552045283477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6701887225524138787422605 2513207709571552045283477)
              ·
                refine ⟨117806611386166502122663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2513207709571552045283477 117806611386166502122663)
                ·
                  rfl

theorem cell19_387159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_387159 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387159 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387159 prefixEnd_387159 := by exact prefixLift 387159
  have htrace : WordTrace (prefixWord ++ tailWord_387159) baseStart_387159 baseEnd_387159 := by
    simpa [prefixWord, tailWord_387159, baseEnd_387159] using wordTrace_append hprefix tailTrace_387159
  have hstable : (prefixWord ++ tailWord_387159).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387159).length < 2 ^ (prefixWord ++ tailWord_387159).sum := by decide
  have hdescent : baseEnd_387159 < baseStart_387159 := by decide
  rcases family_descends (prefixWord ++ tailWord_387159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387197 : List Nat := [1, 4, 1, 1, 3, 9]
def baseStart_387197 : Nat := 118140960795 + 387197 * 2 ^ 59
def prefixEnd_387197 : Nat := 4983230072969 + 3 ^ 40 * 387197 * 2
def baseEnd_387197 : Nat := 13090908245532630364235

theorem tailTrace_387197 : CollatzResearch.WordTrace tailWord_387197 prefixEnd_387197 13090908245532630364235 := by
  unfold tailWord_387197
  simp only [CollatzResearch.WordTrace]
  refine ⟨14122234778258871827991845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9414823185505914551994563 14122234778258871827991845)
  ·
    refine ⟨2647919020923538467748471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14122234778258871827991845 2647919020923538467748471)
    ·
      refine ⟨3971878531385307701622707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2647919020923538467748471 3971878531385307701622707)
      ·
        refine ⟨5957817797077961552434061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971878531385307701622707 5957817797077961552434061)
        ·
          refine ⟨2234181673904235582162773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5957817797077961552434061 2234181673904235582162773)
          ·
            refine ⟨13090908245532630364235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2234181673904235582162773 13090908245532630364235)
            ·
              rfl

theorem cell19_387197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 9].length) (baseStart_387197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387197 prefixEnd_387197 := by exact prefixLift 387197
  have htrace : WordTrace (prefixWord ++ tailWord_387197) baseStart_387197 baseEnd_387197 := by
    simpa [prefixWord, tailWord_387197, baseEnd_387197] using wordTrace_append hprefix tailTrace_387197
  have hstable : (prefixWord ++ tailWord_387197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387197).length < 2 ^ (prefixWord ++ tailWord_387197).sum := by decide
  have hdescent : baseEnd_387197 < baseStart_387197 := by decide
  rcases family_descends (prefixWord ++ tailWord_387197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387231 : List Nat := [1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_387231 : Nat := 118140960795 + 387231 * 2 ^ 59
def prefixEnd_387231 : Nat := 4983230072969 + 3 ^ 40 * 387231 * 2
def baseEnd_387231 : Nat := 117828519894091668522467

theorem tailTrace_387231 : CollatzResearch.WordTrace tailWord_387231 prefixEnd_387231 117828519894091668522467 := by
  unfold tailWord_387231
  simp only [CollatzResearch.WordTrace]
  refine ⟨14123474860135695634729547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9415649906757130423153031 14123474860135695634729547)
  ·
    refine ⟨21185212290203543452094321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14123474860135695634729547 21185212290203543452094321)
    ·
      refine ⟨15888909217652657589070741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21185212290203543452094321 15888909217652657589070741)
      ·
        refine ⟨744792619577468324487691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15888909217652657589070741 744792619577468324487691)
        ·
          refine ⟨1117188929366202486731537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744792619577468324487691 1117188929366202486731537)
          ·
            refine ⟨837891697024651865048653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117188929366202486731537 837891697024651865048653)
            ·
              refine ⟨314209386384244449393245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 837891697024651865048653 314209386384244449393245)
              ·
                refine ⟨117828519894091668522467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314209386384244449393245 117828519894091668522467)
                ·
                  rfl

theorem cell19_387231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_387231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387231 prefixEnd_387231 := by exact prefixLift 387231
  have htrace : WordTrace (prefixWord ++ tailWord_387231) baseStart_387231 baseEnd_387231 := by
    simpa [prefixWord, tailWord_387231, baseEnd_387231] using wordTrace_append hprefix tailTrace_387231
  have hstable : (prefixWord ++ tailWord_387231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387231).length < 2 ^ (prefixWord ++ tailWord_387231).sum := by decide
  have hdescent : baseEnd_387231 < baseStart_387231 := by decide
  rcases family_descends (prefixWord ++ tailWord_387231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387286 : List Nat := [5, 2, 1, 2, 1, 1, 4, 3]
def baseStart_387286 : Nat := 118140960795 + 387286 * 2 ^ 59
def prefixEnd_387286 : Nat := 4983230072969 + 3 ^ 40 * 387286 * 2
def baseEnd_387286 : Nat := 117845255559867837300095

theorem tailTrace_387286 : CollatzResearch.WordTrace tailWord_387286 prefixEnd_387286 117845255559867837300095 := by
  unfold tailWord_387286
  simp only [CollatzResearch.WordTrace]
  refine ⟨882842554683527501748857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9416987249957626685321141 882842554683527501748857)
  ·
    refine ⟨662131916012645626311643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 882842554683527501748857 662131916012645626311643)
    ·
      refine ⟨993197874018968439467465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 662131916012645626311643 993197874018968439467465)
      ·
        refine ⟨744898405514226329600599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993197874018968439467465 744898405514226329600599)
        ·
          refine ⟨1117347608271339494400899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744898405514226329600599 1117347608271339494400899)
          ·
            refine ⟨1676021412407009241601349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117347608271339494400899 1676021412407009241601349)
            ·
              refine ⟨314254014826314232800253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1676021412407009241601349 314254014826314232800253)
              ·
                refine ⟨117845255559867837300095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314254014826314232800253 117845255559867837300095)
                ·
                  rfl

theorem cell19_387286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_387286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387286 prefixEnd_387286 := by exact prefixLift 387286
  have htrace : WordTrace (prefixWord ++ tailWord_387286) baseStart_387286 baseEnd_387286 := by
    simpa [prefixWord, tailWord_387286, baseEnd_387286] using wordTrace_append hprefix tailTrace_387286
  have hstable : (prefixWord ++ tailWord_387286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387286).length < 2 ^ (prefixWord ++ tailWord_387286).sum := by decide
  have hdescent : baseEnd_387286 < baseStart_387286 := by decide
  rcases family_descends (prefixWord ++ tailWord_387286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387288 : List Nat := [2, 1, 2, 2, 4, 3, 2, 3]
def baseStart_387288 : Nat := 118140960795 + 387288 * 2 ^ 59
def prefixEnd_387288 : Nat := 4983230072969 + 3 ^ 40 * 387288 * 2
def baseEnd_387288 : Nat := 117845864129532425255645

theorem tailTrace_387288 : CollatzResearch.WordTrace tailWord_387288 prefixEnd_387288 117845864129532425255645 := by
  unfold tailWord_387288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7062776910464597184777259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9417035880619462913036345 7062776910464597184777259)
  ·
    refine ⟨10594165365696895777165889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7062776910464597184777259 10594165365696895777165889)
    ·
      refine ⟨7945624024272671832874417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10594165365696895777165889 7945624024272671832874417)
      ·
        refine ⟨5959218018204503874655813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7945624024272671832874417 5959218018204503874655813)
        ·
          refine ⟨1117353378413344476497965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5959218018204503874655813 1117353378413344476497965)
          ·
            refine ⟨419007516905004178686737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1117353378413344476497965 419007516905004178686737)
            ·
              refine ⟨314255637678753134015053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419007516905004178686737 314255637678753134015053)
              ·
                refine ⟨117845864129532425255645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314255637678753134015053 117845864129532425255645)
                ·
                  rfl

theorem cell19_387288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_387288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387288 prefixEnd_387288 := by exact prefixLift 387288
  have htrace : WordTrace (prefixWord ++ tailWord_387288) baseStart_387288 baseEnd_387288 := by
    simpa [prefixWord, tailWord_387288, baseEnd_387288] using wordTrace_append hprefix tailTrace_387288
  have hstable : (prefixWord ++ tailWord_387288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387288).length < 2 ^ (prefixWord ++ tailWord_387288).sum := by decide
  have hdescent : baseEnd_387288 < baseStart_387288 := by decide
  rcases family_descends (prefixWord ++ tailWord_387288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387290 : List Nat := [3, 1, 1, 2, 2, 1, 6, 3]
def baseStart_387290 : Nat := 118140960795 + 387290 * 2 ^ 59
def prefixEnd_387290 : Nat := 4983230072969 + 3 ^ 40 * 387290 * 2
def baseEnd_387290 : Nat := 117846472699197013211195

theorem tailTrace_387290 : CollatzResearch.WordTrace tailWord_387290 prefixEnd_387290 117846472699197013211195 := by
  unfold tailWord_387290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3531406691730487177781831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9417084511281299140751549 3531406691730487177781831)
  ·
    refine ⟨5297110037595730766672747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3531406691730487177781831 5297110037595730766672747)
    ·
      refine ⟨7945665056393596150009121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5297110037595730766672747 7945665056393596150009121)
      ·
        refine ⟨5959248792295197112506841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7945665056393596150009121 5959248792295197112506841)
        ·
          refine ⟨4469436594221397834380131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5959248792295197112506841 4469436594221397834380131)
          ·
            refine ⟨6704154891332096751570197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4469436594221397834380131 6704154891332096751570197)
            ·
              refine ⟨314257260531192035229853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6704154891332096751570197 314257260531192035229853)
              ·
                refine ⟨117846472699197013211195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314257260531192035229853 117846472699197013211195)
                ·
                  rfl

theorem cell19_387290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3].length) (baseStart_387290 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387290 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387290 prefixEnd_387290 := by exact prefixLift 387290
  have htrace : WordTrace (prefixWord ++ tailWord_387290) baseStart_387290 baseEnd_387290 := by
    simpa [prefixWord, tailWord_387290, baseEnd_387290] using wordTrace_append hprefix tailTrace_387290
  have hstable : (prefixWord ++ tailWord_387290).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387290).length < 2 ^ (prefixWord ++ tailWord_387290).sum := by decide
  have hdescent : baseEnd_387290 < baseStart_387290 := by decide
  rcases family_descends (prefixWord ++ tailWord_387290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387311 : List Nat := [1, 1, 2, 1, 6, 1, 7]
def baseStart_387311 : Nat := 118140960795 + 387311 * 2 ^ 59
def prefixEnd_387311 : Nat := 4983230072969 + 3 ^ 40 * 387311 * 2
def baseEnd_387311 : Nat := 39284287560225062248157

theorem tailTrace_387311 : CollatzResearch.WordTrace tailWord_387311 prefixEnd_387311 39284287560225062248157 := by
  unfold tailWord_387311
  simp only [CollatzResearch.WordTrace]
  refine ⟨14126392699845869297641787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9417595133230579531761191 14126392699845869297641787)
  ·
    refine ⟨21189589049768803946462681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14126392699845869297641787 21189589049768803946462681)
    ·
      refine ⟨15892191787326602959847011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21189589049768803946462681 15892191787326602959847011)
      ·
        refine ⟨23838287680989904439770517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15892191787326602959847011 23838287680989904439770517)
        ·
          refine ⟨1117419735046401770614243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23838287680989904439770517 1117419735046401770614243)
          ·
            refine ⟨1676129602569602655921365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117419735046401770614243 1676129602569602655921365)
            ·
              refine ⟨39284287560225062248157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1676129602569602655921365 39284287560225062248157)
              ·
                rfl

theorem cell19_387311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 7].length) (baseStart_387311 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387311 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387311 prefixEnd_387311 := by exact prefixLift 387311
  have htrace : WordTrace (prefixWord ++ tailWord_387311) baseStart_387311 baseEnd_387311 := by
    simpa [prefixWord, tailWord_387311, baseEnd_387311] using wordTrace_append hprefix tailTrace_387311
  have hstable : (prefixWord ++ tailWord_387311).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387311).length < 2 ^ (prefixWord ++ tailWord_387311).sum := by decide
  have hdescent : baseEnd_387311 < baseStart_387311 := by decide
  rcases family_descends (prefixWord ++ tailWord_387311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387349 : List Nat := [1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_387349 : Nat := 118140960795 + 387349 * 2 ^ 59
def prefixEnd_387349 : Nat := 4983230072969 + 3 ^ 40 * 387349 * 2
def baseEnd_387349 : Nat := 117864425504302357899923

theorem tailTrace_387349 : CollatzResearch.WordTrace tailWord_387349 prefixEnd_387349 117864425504302357899923 := by
  unfold tailWord_387349
  simp only [CollatzResearch.WordTrace]
  refine ⟨14127778673708201787525101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9418519115805467858350067 14127778673708201787525101)
  ·
    refine ⟨5297917002640575670321913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14127778673708201787525101 5297917002640575670321913)
    ·
      refine ⟨3973437751980431752741435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5297917002640575670321913 3973437751980431752741435)
      ·
        refine ⟨5960156627970647629112153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3973437751980431752741435 5960156627970647629112153)
        ·
          refine ⟨4470117470977985721834115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5960156627970647629112153 4470117470977985721834115)
          ·
            refine ⟨6705176206466978582751173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4470117470977985721834115 6705176206466978582751173)
            ·
              refine ⟨1257220538712558484265845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6705176206466978582751173 1257220538712558484265845)
              ·
                refine ⟨117864425504302357899923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1257220538712558484265845 117864425504302357899923)
                ·
                  rfl

theorem cell19_387349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_387349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387349 prefixEnd_387349 := by exact prefixLift 387349
  have htrace : WordTrace (prefixWord ++ tailWord_387349) baseStart_387349 baseEnd_387349 := by
    simpa [prefixWord, tailWord_387349, baseEnd_387349] using wordTrace_append hprefix tailTrace_387349
  have hstable : (prefixWord ++ tailWord_387349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387349).length < 2 ^ (prefixWord ++ tailWord_387349).sum := by decide
  have hdescent : baseEnd_387349 < baseStart_387349 := by decide
  rcases family_descends (prefixWord ++ tailWord_387349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387368 : List Nat := [2, 1, 5, 1, 10]
def baseStart_387368 : Nat := 118140960795 + 387368 * 2 ^ 59
def prefixEnd_387368 : Nat := 4983230072969 + 3 ^ 40 * 387368 * 2
def baseEnd_387368 : Nat := 4365563219115405313987

theorem tailTrace_387368 : CollatzResearch.WordTrace tailWord_387368 prefixEnd_387368 4365563219115405313987 := by
  unfold tailWord_387368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064235830319684016233379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9418981107092912021644505 7064235830319684016233379)
  ·
    refine ⟨10596353745479526024350069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7064235830319684016233379 10596353745479526024350069)
    ·
      refine ⟨993408163638705564782819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10596353745479526024350069 993408163638705564782819)
      ·
        refine ⟨1490112245458058347174229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993408163638705564782819 1490112245458058347174229)
        ·
          refine ⟨4365563219115405313987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1490112245458058347174229 4365563219115405313987)
          ·
            rfl

theorem cell19_387368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 10].length) (baseStart_387368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387368 prefixEnd_387368 := by exact prefixLift 387368
  have htrace : WordTrace (prefixWord ++ tailWord_387368) baseStart_387368 baseEnd_387368 := by
    simpa [prefixWord, tailWord_387368, baseEnd_387368] using wordTrace_append hprefix tailTrace_387368
  have hstable : (prefixWord ++ tailWord_387368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387368).length < 2 ^ (prefixWord ++ tailWord_387368).sum := by decide
  have hdescent : baseEnd_387368 < baseStart_387368 := by decide
  rcases family_descends (prefixWord ++ tailWord_387368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387385 : List Nat := [1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_387385 : Nat := 118140960795 + 387385 * 2 ^ 59
def prefixEnd_387385 : Nat := 4983230072969 + 3 ^ 40 * 387385 * 2
def baseEnd_387385 : Nat := 117875379758264941099825

theorem tailTrace_387385 : CollatzResearch.WordTrace tailWord_387385 prefixEnd_387385 117875379758264941099825 := by
  unfold tailWord_387385
  simp only [CollatzResearch.WordTrace]
  refine ⟨14129091701577779935835609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9419394467718519957223739 14129091701577779935835609)
  ·
    refine ⟨10596818776183334951876707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14129091701577779935835609 10596818776183334951876707)
    ·
      refine ⟨15895228164275002427815061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10596818776183334951876707 15895228164275002427815061)
      ·
        refine ⟨745088820200390738803831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15895228164275002427815061 745088820200390738803831)
        ·
          refine ⟨1117633230300586108205747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745088820200390738803831 1117633230300586108205747)
          ·
            refine ⟨1676449845450879162308621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117633230300586108205747 1676449845450879162308621)
            ·
              refine ⟨628668692044079685865733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1676449845450879162308621 628668692044079685865733)
              ·
                refine ⟨117875379758264941099825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 628668692044079685865733 117875379758264941099825)
                ·
                  rfl

theorem cell19_387385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_387385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387385 prefixEnd_387385 := by exact prefixLift 387385
  have htrace : WordTrace (prefixWord ++ tailWord_387385) baseStart_387385 baseEnd_387385 := by
    simpa [prefixWord, tailWord_387385, baseEnd_387385] using wordTrace_append hprefix tailTrace_387385
  have hstable : (prefixWord ++ tailWord_387385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387385).length < 2 ^ (prefixWord ++ tailWord_387385).sum := by decide
  have hdescent : baseEnd_387385 < baseStart_387385 := by decide
  rcases family_descends (prefixWord ++ tailWord_387385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387404 : List Nat := [2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_387404 : Nat := 118140960795 + 387404 * 2 ^ 59
def prefixEnd_387404 : Nat := 4983230072969 + 3 ^ 40 * 387404 * 2
def baseEnd_387404 : Nat := 117881161170078526677551

theorem tailTrace_387404 : CollatzResearch.WordTrace tailWord_387404 prefixEnd_387404 117881161170078526677551 := by
  unfold tailWord_387404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7064892344254473090388633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9419856459005964120518177 7064892344254473090388633)
  ·
    refine ⟨5298669258190854817791475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7064892344254473090388633 5298669258190854817791475)
    ·
      refine ⟨7948003887286282226687213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5298669258190854817791475 7948003887286282226687213)
      ·
        refine ⟨2980501457732355835007705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7948003887286282226687213 2980501457732355835007705)
        ·
          refine ⟨2235376093299266876255779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980501457732355835007705 2235376093299266876255779)
          ·
            refine ⟨3353064139948900314383669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235376093299266876255779 3353064139948900314383669)
            ·
              refine ⟨314349763120209404473469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3353064139948900314383669 314349763120209404473469)
              ·
                refine ⟨117881161170078526677551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314349763120209404473469 117881161170078526677551)
                ·
                  rfl

theorem cell19_387404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_387404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387404 prefixEnd_387404 := by exact prefixLift 387404
  have htrace : WordTrace (prefixWord ++ tailWord_387404) baseStart_387404 baseEnd_387404 := by
    simpa [prefixWord, tailWord_387404, baseEnd_387404] using wordTrace_append hprefix tailTrace_387404
  have hstable : (prefixWord ++ tailWord_387404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387404).length < 2 ^ (prefixWord ++ tailWord_387404).sum := by decide
  have hdescent : baseEnd_387404 < baseStart_387404 := by decide
  rcases family_descends (prefixWord ++ tailWord_387404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387459 : List Nat := [1, 1, 1, 3, 6, 2, 2, 3]
def baseStart_387459 : Nat := 118140960795 + 387459 * 2 ^ 59
def prefixEnd_387459 : Nat := 4983230072969 + 3 ^ 40 * 387459 * 2
def baseEnd_387459 : Nat := 117897896835854695455179

theorem tailTrace_387459 : CollatzResearch.WordTrace tailWord_387459 prefixEnd_387459 117897896835854695455179 := by
  unfold tailWord_387459
  simp only [CollatzResearch.WordTrace]
  refine ⟨14131790703309690574029431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9421193802206460382686287 14131790703309690574029431)
  ·
    refine ⟨21197686054964535861044147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14131790703309690574029431 21197686054964535861044147)
    ·
      refine ⟨31796529082446803791566221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21197686054964535861044147 31796529082446803791566221)
      ·
        refine ⟨11923698405917551421837333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31796529082446803791566221 11923698405917551421837333)
        ·
          refine ⟨558923362777385222898625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11923698405917551421837333 558923362777385222898625)
          ·
            refine ⟨419192522083038917173969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558923362777385222898625 419192522083038917173969)
            ·
              refine ⟨314394391562279187880477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419192522083038917173969 314394391562279187880477)
              ·
                refine ⟨117897896835854695455179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 314394391562279187880477 117897896835854695455179)
                ·
                  rfl

theorem cell19_387459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 3].length) (baseStart_387459 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387459 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387459 prefixEnd_387459 := by exact prefixLift 387459
  have htrace : WordTrace (prefixWord ++ tailWord_387459) baseStart_387459 baseEnd_387459 := by
    simpa [prefixWord, tailWord_387459, baseEnd_387459] using wordTrace_append hprefix tailTrace_387459
  have hstable : (prefixWord ++ tailWord_387459).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387459).length < 2 ^ (prefixWord ++ tailWord_387459).sum := by decide
  have hdescent : baseEnd_387459 < baseStart_387459 := by decide
  rcases family_descends (prefixWord ++ tailWord_387459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387463 : List Nat := [1, 1, 4, 2, 2, 1, 3, 5]
def baseStart_387463 : Nat := 118140960795 + 387463 * 2 ^ 59
def prefixEnd_387463 : Nat := 4983230072969 + 3 ^ 40 * 387463 * 2
def baseEnd_387463 : Nat := 117899113975183871366279

theorem tailTrace_387463 : CollatzResearch.WordTrace tailWord_387463 prefixEnd_387463 117899113975183871366279 := by
  unfold tailWord_387463
  simp only [CollatzResearch.WordTrace]
  refine ⟨14131936595295199257175043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9421291063530132838116695 14131936595295199257175043)
  ·
    refine ⟨21197904892942798885762565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14131936595295199257175043 21197904892942798885762565)
    ·
      refine ⟨3974607167426774791080481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21197904892942798885762565 3974607167426774791080481)
      ·
        refine ⟨2980955375570081093310361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3974607167426774791080481 2980955375570081093310361)
        ·
          refine ⟨2235716531677560819982771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2980955375570081093310361 2235716531677560819982771)
          ·
            refine ⟨3353574797516341229974157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235716531677560819982771 3353574797516341229974157)
            ·
              refine ⟨1257590549068627961240309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3353574797516341229974157 1257590549068627961240309)
              ·
                refine ⟨117899113975183871366279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1257590549068627961240309 117899113975183871366279)
                ·
                  rfl

theorem cell19_387463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_387463 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387463 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387463 prefixEnd_387463 := by exact prefixLift 387463
  have htrace : WordTrace (prefixWord ++ tailWord_387463) baseStart_387463 baseEnd_387463 := by
    simpa [prefixWord, tailWord_387463, baseEnd_387463] using wordTrace_append hprefix tailTrace_387463
  have hstable : (prefixWord ++ tailWord_387463).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387463).length < 2 ^ (prefixWord ++ tailWord_387463).sum := by decide
  have hdescent : baseEnd_387463 < baseStart_387463 := by decide
  rcases family_descends (prefixWord ++ tailWord_387463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387480 : List Nat := [2, 1, 2, 5, 1, 3, 5]
def baseStart_387480 : Nat := 118140960795 + 387480 * 2 ^ 59
def prefixEnd_387480 : Nat := 4983230072969 + 3 ^ 40 * 387480 * 2
def baseEnd_387480 : Nat := 39301428939110956329485

theorem tailTrace_387480 : CollatzResearch.WordTrace tailWord_387480 prefixEnd_387480 39301428939110956329485 := by
  unfold tailWord_387480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7066278318116805580271947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9421704424155740773695929 7066278318116805580271947)
  ·
    refine ⟨10599417477175208370407921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7066278318116805580271947 10599417477175208370407921)
    ·
      refine ⟨7949563107881406277805941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10599417477175208370407921 7949563107881406277805941)
      ·
        refine ⟨745271541363881838544307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7949563107881406277805941 745271541363881838544307)
        ·
          refine ⟨1117907312045822757816461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745271541363881838544307 1117907312045822757816461)
          ·
            refine ⟨419215242017183534181173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1117907312045822757816461 419215242017183534181173)
            ·
              refine ⟨39301428939110956329485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 419215242017183534181173 39301428939110956329485)
              ·
                rfl

theorem cell19_387480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_387480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387480 prefixEnd_387480 := by exact prefixLift 387480
  have htrace : WordTrace (prefixWord ++ tailWord_387480) baseStart_387480 baseEnd_387480 := by
    simpa [prefixWord, tailWord_387480, baseEnd_387480] using wordTrace_append hprefix tailTrace_387480
  have hstable : (prefixWord ++ tailWord_387480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387480).length < 2 ^ (prefixWord ++ tailWord_387480).sum := by decide
  have hdescent : baseEnd_387480 < baseStart_387480 := by decide
  rcases family_descends (prefixWord ++ tailWord_387480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387482 : List Nat := [3, 1, 1, 4, 1, 2, 7]
def baseStart_387482 : Nat := 118140960795 + 387482 * 2 ^ 59
def prefixEnd_387482 : Nat := 4983230072969 + 3 ^ 40 * 387482 * 2
def baseEnd_387482 : Nat := 39301631795665818981335

theorem tailTrace_387482 : CollatzResearch.WordTrace tailWord_387482 prefixEnd_387482 39301631795665818981335 := by
  unfold tailWord_387482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533157395556591375529175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9421753054817577001411133 3533157395556591375529175)
  ·
    refine ⟨5299736093334887063293763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533157395556591375529175 5299736093334887063293763)
    ·
      refine ⟨7949604140002330594940645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5299736093334887063293763 7949604140002330594940645)
      ·
        refine ⟨1490550776250436986551371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7949604140002330594940645 1490550776250436986551371)
        ·
          refine ⟨2235826164375655479827057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490550776250436986551371 2235826164375655479827057)
          ·
            refine ⟨1676869623281741609870293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2235826164375655479827057 1676869623281741609870293)
            ·
              refine ⟨39301631795665818981335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1676869623281741609870293 39301631795665818981335)
              ·
                rfl

theorem cell19_387482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_387482 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387482 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387482 prefixEnd_387482 := by exact prefixLift 387482
  have htrace : WordTrace (prefixWord ++ tailWord_387482) baseStart_387482 baseEnd_387482 := by
    simpa [prefixWord, tailWord_387482, baseEnd_387482] using wordTrace_append hprefix tailTrace_387482
  have hstable : (prefixWord ++ tailWord_387482).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387482).length < 2 ^ (prefixWord ++ tailWord_387482).sum := by decide
  have hdescent : baseEnd_387482 < baseStart_387482 := by decide
  rcases family_descends (prefixWord ++ tailWord_387482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387590 : List Nat := [6, 2, 1, 1, 1, 2, 6]
def baseStart_387590 : Nat := 118140960795 + 387590 * 2 ^ 59
def prefixEnd_387590 : Nat := 4983230072969 + 3 ^ 40 * 387590 * 2
def baseEnd_387590 : Nat := 39312586049628402181237

theorem tailTrace_387590 : CollatzResearch.WordTrace tailWord_387590 prefixEnd_387590 39312586049628402181237 := by
  unfold tailWord_387590
  simp only [CollatzResearch.WordTrace]
  refine ⟨441767770807346873345257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9424379110556733298032149 441767770807346873345257)
  ·
    refine ⟨331325828105510155008943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 441767770807346873345257 331325828105510155008943)
    ·
      refine ⟨496988742158265232513415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331325828105510155008943 496988742158265232513415)
      ·
        refine ⟨745483113237397848770123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496988742158265232513415 745483113237397848770123)
        ·
          refine ⟨1118224669856096773155185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745483113237397848770123 1118224669856096773155185)
          ·
            refine ⟨838668502392072579866389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118224669856096773155185 838668502392072579866389)
            ·
              refine ⟨39312586049628402181237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 838668502392072579866389 39312586049628402181237)
              ·
                rfl

theorem cell19_387590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 6].length) (baseStart_387590 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387590 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387590 prefixEnd_387590 := by exact prefixLift 387590
  have htrace : WordTrace (prefixWord ++ tailWord_387590) baseStart_387590 baseEnd_387590 := by
    simpa [prefixWord, tailWord_387590, baseEnd_387590] using wordTrace_append hprefix tailTrace_387590
  have hstable : (prefixWord ++ tailWord_387590).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387590).length < 2 ^ (prefixWord ++ tailWord_387590).sum := by decide
  have hdescent : baseEnd_387590 < baseStart_387590 := by decide
  rcases family_descends (prefixWord ++ tailWord_387590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387596 : List Nat := [2, 2, 1, 2, 4, 2, 6]
def baseStart_387596 : Nat := 118140960795 + 387596 * 2 ^ 59
def prefixEnd_387596 : Nat := 4983230072969 + 3 ^ 40 * 387596 * 2
def baseEnd_387596 : Nat := 39313194619292990136787

theorem tailTrace_387596 : CollatzResearch.WordTrace tailWord_387596 prefixEnd_387596 39313194619292990136787 := by
  unfold tailWord_387596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7068393751906681485883321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9424525002542241981177761 7068393751906681485883321)
  ·
    refine ⟨5301295313930011114412491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7068393751906681485883321 5301295313930011114412491)
    ·
      refine ⟨7951942970895016671618737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5301295313930011114412491 7951942970895016671618737)
      ·
        refine ⟨5963957228171262503714053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7951942970895016671618737 5963957228171262503714053)
        ·
          refine ⟨1118241980282111719446385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5963957228171262503714053 1118241980282111719446385)
          ·
            refine ⟨838681485211583789584789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1118241980282111719446385 838681485211583789584789)
            ·
              refine ⟨39313194619292990136787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 838681485211583789584789 39313194619292990136787)
              ·
                rfl

theorem cell19_387596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_387596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387596 prefixEnd_387596 := by exact prefixLift 387596
  have htrace : WordTrace (prefixWord ++ tailWord_387596) baseStart_387596 baseEnd_387596 := by
    simpa [prefixWord, tailWord_387596, baseEnd_387596] using wordTrace_append hprefix tailTrace_387596
  have hstable : (prefixWord ++ tailWord_387596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387596).length < 2 ^ (prefixWord ++ tailWord_387596).sum := by decide
  have hdescent : baseEnd_387596 < baseStart_387596 := by decide
  rcases family_descends (prefixWord ++ tailWord_387596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387653 : List Nat := [1, 3, 1, 1, 1, 7, 5]
def baseStart_387653 : Nat := 118140960795 + 387653 * 2 ^ 59
def prefixEnd_387653 : Nat := 4983230072969 + 3 ^ 40 * 387653 * 2
def baseEnd_387653 : Nat := 39318976031106575714513

theorem tailTrace_387653 : CollatzResearch.WordTrace tailWord_387653 prefixEnd_387653 39318976031106575714513 := by
  unfold tailWord_387653
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138866464606861706591613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9425910976404574471061075 14138866464606861706591613)
  ·
    refine ⟨5302074924227573139971855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14138866464606861706591613 5302074924227573139971855)
    ·
      refine ⟨7953112386341359709957783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5302074924227573139971855 7953112386341359709957783)
      ·
        refine ⟨11929668579512039564936675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7953112386341359709957783 11929668579512039564936675)
        ·
          refine ⟨17894502869268059347405013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11929668579512039564936675 17894502869268059347405013)
          ·
            refine ⟨419402410998470140954805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17894502869268059347405013 419402410998470140954805)
            ·
              refine ⟨39318976031106575714513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 419402410998470140954805 39318976031106575714513)
              ·
                rfl

theorem cell19_387653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 5].length) (baseStart_387653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387653 prefixEnd_387653 := by exact prefixLift 387653
  have htrace : WordTrace (prefixWord ++ tailWord_387653) baseStart_387653 baseEnd_387653 := by
    simpa [prefixWord, tailWord_387653, baseEnd_387653] using wordTrace_append hprefix tailTrace_387653
  have hstable : (prefixWord ++ tailWord_387653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387653).length < 2 ^ (prefixWord ++ tailWord_387653).sum := by decide
  have hdescent : baseEnd_387653 < baseStart_387653 := by decide
  rcases family_descends (prefixWord ++ tailWord_387653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387712 : List Nat := [2, 1, 1, 2, 1, 12]
def baseStart_387712 : Nat := 118140960795 + 387712 * 2 ^ 59
def prefixEnd_387712 : Nat := 4983230072969 + 3 ^ 40 * 387712 * 2
def baseEnd_387712 : Nat := 13108320099825007981363

theorem tailTrace_387712 : CollatzResearch.WordTrace tailWord_387712 prefixEnd_387712 13108320099825007981363 := by
  unfold tailWord_387712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7070509185696557391494695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9427345580928743188659593 7070509185696557391494695)
  ·
    refine ⟨10605763778544836087242043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7070509185696557391494695 10605763778544836087242043)
    ·
      refine ⟨15908645667817254130863065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10605763778544836087242043 15908645667817254130863065)
      ·
        refine ⟨11931484250862940598147299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15908645667817254130863065 11931484250862940598147299)
        ·
          refine ⟨17897226376294410897220949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11931484250862940598147299 17897226376294410897220949)
          ·
            refine ⟨13108320099825007981363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17897226376294410897220949 13108320099825007981363)
            ·
              rfl

theorem cell19_387712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_387712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387712 prefixEnd_387712 := by exact prefixLift 387712
  have htrace : WordTrace (prefixWord ++ tailWord_387712) baseStart_387712 baseEnd_387712 := by
    simpa [prefixWord, tailWord_387712, baseEnd_387712] using wordTrace_append hprefix tailTrace_387712
  have hstable : (prefixWord ++ tailWord_387712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387712).length < 2 ^ (prefixWord ++ tailWord_387712).sum := by decide
  have hdescent : baseEnd_387712 < baseStart_387712 := by decide
  rcases family_descends (prefixWord ++ tailWord_387712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387767 : List Nat := [1, 1, 3, 1, 6, 1, 6]
def baseStart_387767 : Nat := 118140960795 + 387767 * 2 ^ 59
def prefixEnd_387767 : Nat := 4983230072969 + 3 ^ 40 * 387767 * 2
def baseEnd_387767 : Nat := 39330538854733746869965

theorem tailTrace_387767 : CollatzResearch.WordTrace tailWord_387767 prefixEnd_387767 39330538854733746869965 := by
  unfold tailWord_387767
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143024386193859176241555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9428682924129239450827703 14143024386193859176241555)
  ·
    refine ⟨21214536579290788764362333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14143024386193859176241555 21214536579290788764362333)
    ·
      refine ⟨7955451217234045786635875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21214536579290788764362333 7955451217234045786635875)
      ·
        refine ⟨11933176825851068679953813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7955451217234045786635875 11933176825851068679953813)
        ·
          refine ⟨559367663711768844372835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11933176825851068679953813 559367663711768844372835)
          ·
            refine ⟨839051495567653266559253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559367663711768844372835 839051495567653266559253)
            ·
              refine ⟨39330538854733746869965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 839051495567653266559253 39330538854733746869965)
              ·
                rfl

theorem cell19_387767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_387767 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387767 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387767 prefixEnd_387767 := by exact prefixLift 387767
  have htrace : WordTrace (prefixWord ++ tailWord_387767) baseStart_387767 baseEnd_387767 := by
    simpa [prefixWord, tailWord_387767, baseEnd_387767] using wordTrace_append hprefix tailTrace_387767
  have hstable : (prefixWord ++ tailWord_387767).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387767).length < 2 ^ (prefixWord ++ tailWord_387767).sum := by decide
  have hdescent : baseEnd_387767 < baseStart_387767 := by decide
  rcases family_descends (prefixWord ++ tailWord_387767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387894 : List Nat := [5, 1, 2, 2, 3, 1, 1, 4]
def baseStart_387894 : Nat := 118140960795 + 387894 * 2 ^ 59
def prefixEnd_387894 : Nat := 4983230072969 + 3 ^ 40 * 387894 * 2
def baseEnd_387894 : Nat := 118030260737902575787327

theorem tailTrace_387894 : CollatzResearch.WordTrace tailWord_387894 prefixEnd_387894 118030260737902575787327 := by
  unfold tailWord_387894
  simp only [CollatzResearch.WordTrace]
  refine ⟨884228528545859991632171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9431770971155839910743157 884228528545859991632171)
  ·
    refine ⟨1326342792818789987448257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 884228528545859991632171 1326342792818789987448257)
    ·
      refine ⟨994757094614092490586193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1326342792818789987448257 994757094614092490586193)
      ·
        refine ⟨746067820960569367939645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 994757094614092490586193 746067820960569367939645)
        ·
          refine ⟨279775432860213512977367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 746067820960569367939645 279775432860213512977367)
          ·
            refine ⟨419663149290320269466051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 279775432860213512977367 419663149290320269466051)
            ·
              refine ⟨629494723935480404199077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419663149290320269466051 629494723935480404199077)
              ·
                refine ⟨118030260737902575787327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629494723935480404199077 118030260737902575787327)
                ·
                  rfl

theorem cell19_387894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_387894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387894 prefixEnd_387894 := by exact prefixLift 387894
  have htrace : WordTrace (prefixWord ++ tailWord_387894) baseStart_387894 baseEnd_387894 := by
    simpa [prefixWord, tailWord_387894, baseEnd_387894] using wordTrace_append hprefix tailTrace_387894
  have hstable : (prefixWord ++ tailWord_387894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387894).length < 2 ^ (prefixWord ++ tailWord_387894).sum := by decide
  have hdescent : baseEnd_387894 < baseStart_387894 := by decide
  rcases family_descends (prefixWord ++ tailWord_387894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387898 : List Nat := [3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_387898 : Nat := 118140960795 + 387898 * 2 ^ 59
def prefixEnd_387898 : Nat := 4983230072969 + 3 ^ 40 * 387898 * 2
def baseEnd_387898 : Nat := 118031477877231751698427

theorem tailTrace_387898 : CollatzResearch.WordTrace tailWord_387898 prefixEnd_387898 118031477877231751698427 := by
  unfold tailWord_387898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3536950587179817137315087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9431868232479512366173565 3536950587179817137315087)
  ·
    refine ⟨5305425880769725705972631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3536950587179817137315087 5305425880769725705972631)
    ·
      refine ⟨7958138821154588558958947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5305425880769725705972631 7958138821154588558958947)
      ·
        refine ⟨11937208231731882838438421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7958138821154588558958947 11937208231731882838438421)
        ·
          refine ⟨559556635862432008051801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11937208231731882838438421 559556635862432008051801)
          ·
            refine ⟨419667476896824006038851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559556635862432008051801 419667476896824006038851)
            ·
              refine ⟨629501215345236009058277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419667476896824006038851 629501215345236009058277)
              ·
                refine ⟨118031477877231751698427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629501215345236009058277 118031477877231751698427)
                ·
                  rfl

theorem cell19_387898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_387898 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387898 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387898 prefixEnd_387898 := by exact prefixLift 387898
  have htrace : WordTrace (prefixWord ++ tailWord_387898) baseStart_387898 baseEnd_387898 := by
    simpa [prefixWord, tailWord_387898, baseEnd_387898] using wordTrace_append hprefix tailTrace_387898
  have hstable : (prefixWord ++ tailWord_387898).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387898).length < 2 ^ (prefixWord ++ tailWord_387898).sum := by decide
  have hdescent : baseEnd_387898 < baseStart_387898 := by decide
  rcases family_descends (prefixWord ++ tailWord_387898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387976 : List Nat := [2, 1, 3, 3, 2, 2, 1, 5]
def baseStart_387976 : Nat := 118140960795 + 387976 * 2 ^ 59
def prefixEnd_387976 : Nat := 4983230072969 + 3 ^ 40 * 387976 * 2
def baseEnd_387976 : Nat := 118055212094150681964881

theorem tailTrace_387976 : CollatzResearch.WordTrace tailWord_387976 prefixEnd_387976 118055212094150681964881 := by
  unfold tailWord_387976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075323621218343935299891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9433764828291125247066521 7075323621218343935299891)
  ·
    refine ⟨10612985431827515902949837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7075323621218343935299891 10612985431827515902949837)
    ·
      refine ⟨3979869536935318463606189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10612985431827515902949837 3979869536935318463606189)
      ·
        refine ⟨1492451076350744423852321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3979869536935318463606189 1492451076350744423852321)
        ·
          refine ⟨1119338307263058317889241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492451076350744423852321 1119338307263058317889241)
          ·
            refine ⟨839503730447293738416931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119338307263058317889241 839503730447293738416931)
            ·
              refine ⟨1259255595670940607625397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839503730447293738416931 1259255595670940607625397)
              ·
                refine ⟨118055212094150681964881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1259255595670940607625397 118055212094150681964881)
                ·
                  rfl

theorem cell19_387976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_387976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_387976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_387976 prefixEnd_387976 := by exact prefixLift 387976
  have htrace : WordTrace (prefixWord ++ tailWord_387976) baseStart_387976 baseEnd_387976 := by
    simpa [prefixWord, tailWord_387976, baseEnd_387976] using wordTrace_append hprefix tailTrace_387976
  have hstable : (prefixWord ++ tailWord_387976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387976).length < 2 ^ (prefixWord ++ tailWord_387976).sum := by decide
  have hdescent : baseEnd_387976 < baseStart_387976 := by decide
  rcases family_descends (prefixWord ++ tailWord_387976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388071 : List Nat := [1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_388071 : Nat := 118140960795 + 388071 * 2 ^ 59
def prefixEnd_388071 : Nat := 4983230072969 + 3 ^ 40 * 388071 * 2
def baseEnd_388071 : Nat := 118084119153218609853511

theorem tailTrace_388071 : CollatzResearch.WordTrace tailWord_388071 prefixEnd_388071 118084119153218609853511 := by
  unfold tailWord_388071
  simp only [CollatzResearch.WordTrace]
  refine ⟨14154112177092519095308067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9436074784728346063538711 14154112177092519095308067)
  ·
    refine ⟨21231168265638778642962101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14154112177092519095308067 21231168265638778642962101)
    ·
      refine ⟨1990422024903635497777697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21231168265638778642962101 1990422024903635497777697)
      ·
        refine ⟨1492816518677726623333273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1990422024903635497777697 1492816518677726623333273)
        ·
          refine ⟨1119612389008294967499955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1492816518677726623333273 1119612389008294967499955)
          ·
            refine ⟨1679418583512442451249933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119612389008294967499955 1679418583512442451249933)
            ·
              refine ⟨629781968817165919218725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1679418583512442451249933 629781968817165919218725)
              ·
                refine ⟨118084119153218609853511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 629781968817165919218725 118084119153218609853511)
                ·
                  rfl

theorem cell19_388071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_388071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388071 prefixEnd_388071 := by exact prefixLift 388071
  have htrace : WordTrace (prefixWord ++ tailWord_388071) baseStart_388071 baseEnd_388071 := by
    simpa [prefixWord, tailWord_388071, baseEnd_388071] using wordTrace_append hprefix tailTrace_388071
  have hstable : (prefixWord ++ tailWord_388071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388071).length < 2 ^ (prefixWord ++ tailWord_388071).sum := by decide
  have hdescent : baseEnd_388071 < baseStart_388071 := by decide
  rcases family_descends (prefixWord ++ tailWord_388071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388225 : List Nat := [1, 2, 4, 2, 2, 8]
def baseStart_388225 : Nat := 118140960795 + 388225 * 2 ^ 59
def prefixEnd_388225 : Nat := 4983230072969 + 3 ^ 40 * 388225 * 2
def baseEnd_388225 : Nat := 13125664335265764714541

theorem tailTrace_388225 : CollatzResearch.WordTrace tailWord_388225 prefixEnd_388225 13125664335265764714541 := by
  unfold tailWord_388225
  simp only [CollatzResearch.WordTrace]
  refine ⟨14159729018534603396414129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9439819345689735597609419 14159729018534603396414129)
  ·
    refine ⟨10619796763900952547310597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14159729018534603396414129 10619796763900952547310597)
    ·
      refine ⟨1991211893231428602620737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10619796763900952547310597 1991211893231428602620737)
      ·
        refine ⟨1493408919923571451965553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1991211893231428602620737 1493408919923571451965553)
        ·
          refine ⟨1120056689942678588974165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493408919923571451965553 1120056689942678588974165)
          ·
            refine ⟨13125664335265764714541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1120056689942678588974165 13125664335265764714541)
            ·
              rfl

theorem cell19_388225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 8].length) (baseStart_388225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388225 prefixEnd_388225 := by exact prefixLift 388225
  have htrace : WordTrace (prefixWord ++ tailWord_388225) baseStart_388225 baseEnd_388225 := by
    simpa [prefixWord, tailWord_388225, baseEnd_388225] using wordTrace_append hprefix tailTrace_388225
  have hstable : (prefixWord ++ tailWord_388225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388225).length < 2 ^ (prefixWord ++ tailWord_388225).sum := by decide
  have hdescent : baseEnd_388225 < baseStart_388225 := by decide
  rcases family_descends (prefixWord ++ tailWord_388225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388242 : List Nat := [3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_388242 : Nat := 118140960795 + 388242 * 2 ^ 59
def prefixEnd_388242 : Nat := 4983230072969 + 3 ^ 40 * 388242 * 2
def baseEnd_388242 : Nat := 118136151859540880053045

theorem tailTrace_388242 : CollatzResearch.WordTrace tailWord_388242 prefixEnd_388242 118136151859540880053045 := by
  unfold tailWord_388242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3540087264868253824945745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9440232706315343533188653 3540087264868253824945745)
  ·
    refine ⟨2655065448651190368709309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3540087264868253824945745 2655065448651190368709309)
    ·
      refine ⟨995649543244196388265991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2655065448651190368709309 995649543244196388265991)
      ·
        refine ⟨1493474314866294582398987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995649543244196388265991 1493474314866294582398987)
        ·
          refine ⟨2240211472299441873598481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493474314866294582398987 2240211472299441873598481)
          ·
            refine ⟨1680158604224581405198861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2240211472299441873598481 1680158604224581405198861)
            ·
              refine ⟨630059476584218026949573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1680158604224581405198861 630059476584218026949573)
              ·
                refine ⟨118136151859540880053045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630059476584218026949573 118136151859540880053045)
                ·
                  rfl

theorem cell19_388242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_388242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388242 prefixEnd_388242 := by exact prefixLift 388242
  have htrace : WordTrace (prefixWord ++ tailWord_388242) baseStart_388242 baseEnd_388242 := by
    simpa [prefixWord, tailWord_388242, baseEnd_388242] using wordTrace_append hprefix tailTrace_388242
  have hstable : (prefixWord ++ tailWord_388242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388242).length < 2 ^ (prefixWord ++ tailWord_388242).sum := by decide
  have hdescent : baseEnd_388242 < baseStart_388242 := by decide
  rcases family_descends (prefixWord ++ tailWord_388242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388261 : List Nat := [1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_388261 : Nat := 118140960795 + 388261 * 2 ^ 59
def prefixEnd_388261 : Nat := 4983230072969 + 3 ^ 40 * 388261 * 2
def baseEnd_388261 : Nat := 118141933271354465630771

theorem tailTrace_388261 : CollatzResearch.WordTrace tailWord_388261 prefixEnd_388261 118141933271354465630771 := by
  unfold tailWord_388261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14161042046404181544724637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9440694697602787696483091 14161042046404181544724637)
  ·
    refine ⟨5310390767401568079271739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14161042046404181544724637 5310390767401568079271739)
    ·
      refine ⟨7965586151102352118907609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5310390767401568079271739 7965586151102352118907609)
      ·
        refine ⟨5974189613326764089180707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7965586151102352118907609 5974189613326764089180707)
        ·
          refine ⟨8961284419990146133771061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5974189613326764089180707 8961284419990146133771061)
          ·
            refine ⟨840120414374076200041037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8961284419990146133771061 840120414374076200041037)
            ·
              refine ⟨315045155390278575015389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840120414374076200041037 315045155390278575015389)
              ·
                refine ⟨118141933271354465630771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315045155390278575015389 118141933271354465630771)
                ·
                  rfl

theorem cell19_388261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_388261 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388261 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388261 prefixEnd_388261 := by exact prefixLift 388261
  have htrace : WordTrace (prefixWord ++ tailWord_388261) baseStart_388261 baseEnd_388261 := by
    simpa [prefixWord, tailWord_388261, baseEnd_388261] using wordTrace_append hprefix tailTrace_388261
  have hstable : (prefixWord ++ tailWord_388261).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388261).length < 2 ^ (prefixWord ++ tailWord_388261).sum := by decide
  have hdescent : baseEnd_388261 < baseStart_388261 := by decide
  rcases family_descends (prefixWord ++ tailWord_388261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388320 : List Nat := [2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_388320 : Nat := 118140960795 + 388320 * 2 ^ 59
def prefixEnd_388320 : Nat := 4983230072969 + 3 ^ 40 * 388320 * 2
def baseEnd_388320 : Nat := 118159886076459810319499

theorem tailTrace_388320 : CollatzResearch.WordTrace tailWord_388320 prefixEnd_388320 118159886076459810319499 := by
  unfold tailWord_388320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081596976595217310561207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9442129302126956414081609 7081596976595217310561207)
  ·
    refine ⟨10622395464892825965841811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7081596976595217310561207 10622395464892825965841811)
    ·
      refine ⟨15933593197339238948762717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10622395464892825965841811 15933593197339238948762717)
      ·
        refine ⟨5975097449002214605786019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15933593197339238948762717 5975097449002214605786019)
        ·
          refine ⟨8962646173503321908679029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5975097449002214605786019 8962646173503321908679029)
          ·
            refine ⟨840248078765936428938659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8962646173503321908679029 840248078765936428938659)
            ·
              refine ⟨1260372118148904643407989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840248078765936428938659 1260372118148904643407989)
              ·
                refine ⟨118159886076459810319499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1260372118148904643407989 118159886076459810319499)
                ·
                  rfl

theorem cell19_388320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_388320 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388320 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388320 prefixEnd_388320 := by exact prefixLift 388320
  have htrace : WordTrace (prefixWord ++ tailWord_388320) baseStart_388320 baseEnd_388320 := by
    simpa [prefixWord, tailWord_388320, baseEnd_388320] using wordTrace_append hprefix tailTrace_388320
  have hstable : (prefixWord ++ tailWord_388320).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388320).length < 2 ^ (prefixWord ++ tailWord_388320).sum := by decide
  have hdescent : baseEnd_388320 < baseStart_388320 := by decide
  rcases family_descends (prefixWord ++ tailWord_388320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388339 : List Nat := [1, 1, 1, 2, 2, 7, 5]
def baseStart_388339 : Nat := 118140960795 + 388339 * 2 ^ 59
def prefixEnd_388339 : Nat := 4983230072969 + 3 ^ 40 * 388339 * 2
def baseEnd_388339 : Nat := 39388555829424465299075

theorem tailTrace_388339 : CollatzResearch.WordTrace tailWord_388339 prefixEnd_388339 39388555829424465299075 := by
  unfold tailWord_388339
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163886940121600866064071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9442591293414400577376047 14163886940121600866064071)
  ·
    refine ⟨21245830410182401299096107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14163886940121600866064071 21245830410182401299096107)
    ·
      refine ⟨31868745615273601948644161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21245830410182401299096107 31868745615273601948644161)
      ·
        refine ⟨23901559211455201461483121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31868745615273601948644161 23901559211455201461483121)
        ·
          refine ⟨17926169408591401096112341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23901559211455201461483121 17926169408591401096112341)
          ·
            refine ⟨420144595513860963190133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17926169408591401096112341 420144595513860963190133)
            ·
              refine ⟨39388555829424465299075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420144595513860963190133 39388555829424465299075)
              ·
                rfl

theorem cell19_388339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 5].length) (baseStart_388339 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388339 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388339 prefixEnd_388339 := by exact prefixLift 388339
  have htrace : WordTrace (prefixWord ++ tailWord_388339) baseStart_388339 baseEnd_388339 := by
    simpa [prefixWord, tailWord_388339, baseEnd_388339] using wordTrace_append hprefix tailTrace_388339
  have hstable : (prefixWord ++ tailWord_388339).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388339).length < 2 ^ (prefixWord ++ tailWord_388339).sum := by decide
  have hdescent : baseEnd_388339 < baseStart_388339 := by decide
  rcases family_descends (prefixWord ++ tailWord_388339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388354 : List Nat := [3, 4, 1, 1, 3, 1, 2, 4]
def baseStart_388354 : Nat := 118140960795 + 388354 * 2 ^ 59
def prefixEnd_388354 : Nat := 4983230072969 + 3 ^ 40 * 388354 * 2
def baseEnd_388354 : Nat := 118170231760757805563851

theorem tailTrace_388354 : CollatzResearch.WordTrace tailWord_388354 prefixEnd_388354 118170231760757805563851 := by
  unfold tailWord_388354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3541108508766814606965029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9442956023378172285240077 3541108508766814606965029)
  ·
    refine ⟨663957845393777738805943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3541108508766814606965029 663957845393777738805943)
    ·
      refine ⟨995936768090666608208915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663957845393777738805943 995936768090666608208915)
      ·
        refine ⟨1493905152135999912313373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995936768090666608208915 1493905152135999912313373)
        ·
          refine ⟨560214432050999967117515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1493905152135999912313373 560214432050999967117515)
          ·
            refine ⟨840321648076499950676273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560214432050999967117515 840321648076499950676273)
            ·
              refine ⟨630241236057374963007205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840321648076499950676273 630241236057374963007205)
              ·
                refine ⟨118170231760757805563851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630241236057374963007205 118170231760757805563851)
                ·
                  rfl

theorem cell19_388354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_388354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388354 prefixEnd_388354 := by exact prefixLift 388354
  have htrace : WordTrace (prefixWord ++ tailWord_388354) baseStart_388354 baseEnd_388354 := by
    simpa [prefixWord, tailWord_388354, baseEnd_388354] using wordTrace_append hprefix tailTrace_388354
  have hstable : (prefixWord ++ tailWord_388354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388354).length < 2 ^ (prefixWord ++ tailWord_388354).sum := by decide
  have hdescent : baseEnd_388354 < baseStart_388354 := by decide
  rcases family_descends (prefixWord ++ tailWord_388354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388356 : List Nat := [2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_388356 : Nat := 118140960795 + 388356 * 2 ^ 59
def prefixEnd_388356 : Nat := 4983230072969 + 3 ^ 40 * 388356 * 2
def baseEnd_388356 : Nat := 118170840330422393519401

theorem tailTrace_388356 : CollatzResearch.WordTrace tailWord_388356 prefixEnd_388356 118170840330422393519401 := by
  unfold tailWord_388356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7082253490530006384716461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9443004654040008512955281 7082253490530006384716461)
  ·
    refine ⟨2655845058948752394268673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7082253490530006384716461 2655845058948752394268673)
    ·
      refine ⟨1991883794211564295701505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2655845058948752394268673 1991883794211564295701505)
      ·
        refine ⟨1493912845658673221776129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1991883794211564295701505 1493912845658673221776129)
        ·
          refine ⟨1120434634244004916332097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1493912845658673221776129 1120434634244004916332097)
          ·
            refine ⟨840325975683003687249073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120434634244004916332097 840325975683003687249073)
            ·
              refine ⟨630244481762252765436805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840325975683003687249073 630244481762252765436805)
              ·
                refine ⟨118170840330422393519401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630244481762252765436805 118170840330422393519401)
                ·
                  rfl

theorem cell19_388356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_388356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388356 prefixEnd_388356 := by exact prefixLift 388356
  have htrace : WordTrace (prefixWord ++ tailWord_388356) baseStart_388356 baseEnd_388356 := by
    simpa [prefixWord, tailWord_388356, baseEnd_388356] using wordTrace_append hprefix tailTrace_388356
  have hstable : (prefixWord ++ tailWord_388356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388356).length < 2 ^ (prefixWord ++ tailWord_388356).sum := by decide
  have hdescent : baseEnd_388356 < baseStart_388356 := by decide
  rcases family_descends (prefixWord ++ tailWord_388356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388415 : List Nat := [1, 1, 2, 2, 4, 2, 3, 4]
def baseStart_388415 : Nat := 118140960795 + 388415 * 2 ^ 59
def prefixEnd_388415 : Nat := 4983230072969 + 3 ^ 40 * 388415 * 2
def baseEnd_388415 : Nat := 118188793135527738208129

theorem tailTrace_388415 : CollatzResearch.WordTrace tailWord_388415 prefixEnd_388415 118188793135527738208129 := by
  unfold tailWord_388415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14166658887846265845830699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9444439258564177230553799 14166658887846265845830699)
  ·
    refine ⟨21249988331769398768746049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14166658887846265845830699 21249988331769398768746049)
    ·
      refine ⟨15937491248827049076559537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21249988331769398768746049 15937491248827049076559537)
      ·
        refine ⟨11953118436620286807419653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15937491248827049076559537 11953118436620286807419653)
        ·
          refine ⟨2241209706866303776391185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11953118436620286807419653 2241209706866303776391185)
          ·
            refine ⟨1680907280149727832293389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2241209706866303776391185 1680907280149727832293389)
            ·
              refine ⟨630340230056147937110021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1680907280149727832293389 630340230056147937110021)
              ·
                refine ⟨118188793135527738208129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630340230056147937110021 118188793135527738208129)
                ·
                  rfl

theorem cell19_388415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_388415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388415 prefixEnd_388415 := by exact prefixLift 388415
  have htrace : WordTrace (prefixWord ++ tailWord_388415) baseStart_388415 baseEnd_388415 := by
    simpa [prefixWord, tailWord_388415, baseEnd_388415] using wordTrace_append hprefix tailTrace_388415
  have hstable : (prefixWord ++ tailWord_388415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388415).length < 2 ^ (prefixWord ++ tailWord_388415).sum := by decide
  have hdescent : baseEnd_388415 < baseStart_388415 := by decide
  rcases family_descends (prefixWord ++ tailWord_388415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388529 : List Nat := [1, 2, 2, 4, 1, 1, 4, 4]
def baseStart_388529 : Nat := 118140960795 + 388529 * 2 ^ 59
def prefixEnd_388529 : Nat := 4983230072969 + 3 ^ 40 * 388529 * 2
def baseEnd_388529 : Nat := 118223481606409251674485

theorem tailTrace_388529 : CollatzResearch.WordTrace tailWord_388529 prefixEnd_388529 118223481606409251674485 := by
  unfold tailWord_388529
  simp only [CollatzResearch.WordTrace]
  refine ⟨14170816809433263315480641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9447211206288842210320427 14170816809433263315480641)
  ·
    refine ⟨10628112607074947486610481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14170816809433263315480641 10628112607074947486610481)
    ·
      refine ⟨7971084455306210614957861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10628112607074947486610481 7971084455306210614957861)
      ·
        refine ⟨1494578335369914490304599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7971084455306210614957861 1494578335369914490304599)
        ·
          refine ⟨2241867503054871735456899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494578335369914490304599 2241867503054871735456899)
          ·
            refine ⟨3362801254582307603185349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2241867503054871735456899 3362801254582307603185349)
            ·
              refine ⟨630525235234182675597253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3362801254582307603185349 630525235234182675597253)
              ·
                refine ⟨118223481606409251674485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630525235234182675597253 118223481606409251674485)
                ·
                  rfl

theorem cell19_388529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_388529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388529 prefixEnd_388529 := by exact prefixLift 388529
  have htrace : WordTrace (prefixWord ++ tailWord_388529) baseStart_388529 baseEnd_388529 := by
    simpa [prefixWord, tailWord_388529, baseEnd_388529] using wordTrace_append hprefix tailTrace_388529
  have hstable : (prefixWord ++ tailWord_388529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388529).length < 2 ^ (prefixWord ++ tailWord_388529).sum := by decide
  have hdescent : baseEnd_388529 < baseStart_388529 := by decide
  rcases family_descends (prefixWord ++ tailWord_388529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388569 : List Nat := [1, 2, 1, 2, 4, 9]
def baseStart_388569 : Nat := 118140960795 + 388569 * 2 ^ 59
def prefixEnd_388569 : Nat := 4983230072969 + 3 ^ 40 * 388569 * 2
def baseEnd_388569 : Nat := 13137294777744556753943

theorem tailTrace_388569 : CollatzResearch.WordTrace tailWord_388569 prefixEnd_388569 13137294777744556753943 := by
  unfold tailWord_388569
  simp only [CollatzResearch.WordTrace]
  refine ⟨14172275729288350146936761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9448183819525566764624507 14172275729288350146936761)
  ·
    refine ⟨10629206796966262610202571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14172275729288350146936761 10629206796966262610202571)
    ·
      refine ⟨15943810195449393915303857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10629206796966262610202571 15943810195449393915303857)
      ·
        refine ⟨11957857646587045436477893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15943810195449393915303857 11957857646587045436477893)
        ·
          refine ⟨2242098308735071019339605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11957857646587045436477893 2242098308735071019339605)
          ·
            refine ⟨13137294777744556753943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2242098308735071019339605 13137294777744556753943)
            ·
              rfl

theorem cell19_388569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_388569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388569 prefixEnd_388569 := by exact prefixLift 388569
  have htrace : WordTrace (prefixWord ++ tailWord_388569) baseStart_388569 baseEnd_388569 := by
    simpa [prefixWord, tailWord_388569, baseEnd_388569] using wordTrace_append hprefix tailTrace_388569
  have hstable : (prefixWord ++ tailWord_388569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388569).length < 2 ^ (prefixWord ++ tailWord_388569).sum := by decide
  have hdescent : baseEnd_388569 < baseStart_388569 := by decide
  rcases family_descends (prefixWord ++ tailWord_388569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388588 : List Nat := [2, 2, 1, 1, 2, 1, 2, 8]
def baseStart_388588 : Nat := 118140960795 + 388588 * 2 ^ 59
def prefixEnd_388588 : Nat := 4983230072969 + 3 ^ 40 * 388588 * 2
def baseEnd_388588 : Nat := 118241434411514596363213

theorem tailTrace_388588 : CollatzResearch.WordTrace tailWord_388588 prefixEnd_388588 118241434411514596363213 := by
  unfold tailWord_388588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086484358109758195939209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9448645810813010927918945 7086484358109758195939209)
  ·
    refine ⟨5314863268582318646954407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7086484358109758195939209 5314863268582318646954407)
    ·
      refine ⟨7972294902873477970431611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5314863268582318646954407 7972294902873477970431611)
      ·
        refine ⟨11958442354310216955647417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7972294902873477970431611 11958442354310216955647417)
        ·
          refine ⟨8968831765732662716735563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11958442354310216955647417 8968831765732662716735563)
          ·
            refine ⟨13453247648598994075103345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8968831765732662716735563 13453247648598994075103345)
            ·
              refine ⟨10089935736449245556327509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13453247648598994075103345 10089935736449245556327509)
              ·
                refine ⟨118241434411514596363213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10089935736449245556327509 118241434411514596363213)
                ·
                  rfl

theorem cell19_388588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_388588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388588 prefixEnd_388588 := by exact prefixLift 388588
  have htrace : WordTrace (prefixWord ++ tailWord_388588) baseStart_388588 baseEnd_388588 := by
    simpa [prefixWord, tailWord_388588, baseEnd_388588] using wordTrace_append hprefix tailTrace_388588
  have hstable : (prefixWord ++ tailWord_388588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388588).length < 2 ^ (prefixWord ++ tailWord_388588).sum := by decide
  have hdescent : baseEnd_388588 < baseStart_388588 := by decide
  rcases family_descends (prefixWord ++ tailWord_388588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388645 : List Nat := [1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_388645 : Nat := 118140960795 + 388645 * 2 ^ 59
def prefixEnd_388645 : Nat := 4983230072969 + 3 ^ 40 * 388645 * 2
def baseEnd_388645 : Nat := 118258778646955353096391

theorem tailTrace_388645 : CollatzResearch.WordTrace tailWord_388645 prefixEnd_388645 118258778646955353096391 := by
  unfold tailWord_388645
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175047677013015126703389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9450031784675343417802259 14175047677013015126703389)
  ·
    refine ⟨5315642878879880672513771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14175047677013015126703389 5315642878879880672513771)
    ·
      refine ⟨7973464318319821008770657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5315642878879880672513771 7973464318319821008770657)
      ·
        refine ⟨5980098238739865756577993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7973464318319821008770657 5980098238739865756577993)
        ·
          refine ⟨4485073679054899317433495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5980098238739865756577993 4485073679054899317433495)
          ·
            refine ⟨6727610518582348976150243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485073679054899317433495 6727610518582348976150243)
            ·
              refine ⟨10091415777873523464225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6727610518582348976150243 10091415777873523464225365)
              ·
                refine ⟨118258778646955353096391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10091415777873523464225365 118258778646955353096391)
                ·
                  rfl

theorem cell19_388645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_388645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388645 prefixEnd_388645 := by exact prefixLift 388645
  have htrace : WordTrace (prefixWord ++ tailWord_388645) baseStart_388645 baseEnd_388645 := by
    simpa [prefixWord, tailWord_388645, baseEnd_388645] using wordTrace_append hprefix tailTrace_388645
  have hstable : (prefixWord ++ tailWord_388645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388645).length < 2 ^ (prefixWord ++ tailWord_388645).sum := by decide
  have hdescent : baseEnd_388645 < baseStart_388645 := by decide
  rcases family_descends (prefixWord ++ tailWord_388645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388679 : List Nat := [1, 1, 4, 1, 6, 1, 5]
def baseStart_388679 : Nat := 118140960795 + 388679 * 2 ^ 59
def prefixEnd_388679 : Nat := 4983230072969 + 3 ^ 40 * 388679 * 2
def baseEnd_388679 : Nat := 39423041443751116113581

theorem tailTrace_388679 : CollatzResearch.WordTrace tailWord_388679 prefixEnd_388679 39423041443751116113581 := by
  unfold tailWord_388679
  simp only [CollatzResearch.WordTrace]
  refine ⟨14176287758889838933441091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9450858505926559288960727 14176287758889838933441091)
  ·
    refine ⟨21264431638334758400161637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14176287758889838933441091 21264431638334758400161637)
    ·
      refine ⟨3987080932187767200030307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21264431638334758400161637 3987080932187767200030307)
      ·
        refine ⟨5980621398281650800045461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987080932187767200030307 5980621398281650800045461)
        ·
          refine ⟨280341628044452381252131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5980621398281650800045461 280341628044452381252131)
          ·
            refine ⟨420512442066678571878197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280341628044452381252131 420512442066678571878197)
            ·
              refine ⟨39423041443751116113581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420512442066678571878197 39423041443751116113581)
              ·
                rfl

theorem cell19_388679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 5].length) (baseStart_388679 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388679 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388679 prefixEnd_388679 := by exact prefixLift 388679
  have htrace : WordTrace (prefixWord ++ tailWord_388679) baseStart_388679 baseEnd_388679 := by
    simpa [prefixWord, tailWord_388679, baseEnd_388679] using wordTrace_append hprefix tailTrace_388679
  have hstable : (prefixWord ++ tailWord_388679).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388679).length < 2 ^ (prefixWord ++ tailWord_388679).sum := by decide
  have hdescent : baseEnd_388679 < baseStart_388679 := by decide
  rcases family_descends (prefixWord ++ tailWord_388679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388694 : List Nat := [5, 2, 2, 2, 1, 1, 2, 4]
def baseStart_388694 : Nat := 118140960795 + 388694 * 2 ^ 59
def prefixEnd_388694 : Nat := 4983230072969 + 3 ^ 40 * 388694 * 2
def baseEnd_388694 : Nat := 118273688603737758007369

theorem tailTrace_388694 : CollatzResearch.WordTrace tailWord_388694 prefixEnd_388694 118273688603737758007369 := by
  unfold tailWord_388694
  simp only [CollatzResearch.WordTrace]
  refine ⟨886052178364718530952321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9451223235890330996824757 886052178364718530952321)
  ·
    refine ⟨664539133773538898214241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 886052178364718530952321 664539133773538898214241)
    ·
      refine ⟨498404350330154173660681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 664539133773538898214241 498404350330154173660681)
      ·
        refine ⟨373803262747615630245511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498404350330154173660681 373803262747615630245511)
        ·
          refine ⟨560704894121423445368267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373803262747615630245511 560704894121423445368267)
          ·
            refine ⟨841057341182135168052401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560704894121423445368267 841057341182135168052401)
            ·
              refine ⟨630793005886601376039301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841057341182135168052401 630793005886601376039301)
              ·
                refine ⟨118273688603737758007369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 630793005886601376039301 118273688603737758007369)
                ·
                  rfl

theorem cell19_388694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_388694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388694 prefixEnd_388694 := by exact prefixLift 388694
  have htrace : WordTrace (prefixWord ++ tailWord_388694) baseStart_388694 baseEnd_388694 := by
    simpa [prefixWord, tailWord_388694, baseEnd_388694] using wordTrace_append hprefix tailTrace_388694
  have hstable : (prefixWord ++ tailWord_388694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388694).length < 2 ^ (prefixWord ++ tailWord_388694).sum := by decide
  have hdescent : baseEnd_388694 < baseStart_388694 := by decide
  rcases family_descends (prefixWord ++ tailWord_388694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388700 : List Nat := [2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_388700 : Nat := 118140960795 + 388700 * 2 ^ 59
def prefixEnd_388700 : Nat := 4983230072969 + 3 ^ 40 * 388700 * 2
def baseEnd_388700 : Nat := 118275514312731521874019

theorem tailTrace_388700 : CollatzResearch.WordTrace tailWord_388700 prefixEnd_388700 118275514312731521874019 := by
  unfold tailWord_388700
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088526845906879759977777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9451369127875839679970369 7088526845906879759977777)
  ·
    refine ⟨5316395134430159819983333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7088526845906879759977777 5316395134430159819983333)
    ·
      refine ⟨996824087705654966246875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5316395134430159819983333 996824087705654966246875)
      ·
        refine ⟨1495236131558482449370313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996824087705654966246875 1495236131558482449370313)
        ·
          refine ⟨1121427098668861837027735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495236131558482449370313 1121427098668861837027735)
          ·
            refine ⟨1682140648003292755541603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121427098668861837027735 1682140648003292755541603)
            ·
              refine ⟨2523210972004939133312405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1682140648003292755541603 2523210972004939133312405)
              ·
                refine ⟨118275514312731521874019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2523210972004939133312405 118275514312731521874019)
                ·
                  rfl

theorem cell19_388700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_388700 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388700 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388700 prefixEnd_388700 := by exact prefixLift 388700
  have htrace : WordTrace (prefixWord ++ tailWord_388700) baseStart_388700 baseEnd_388700 := by
    simpa [prefixWord, tailWord_388700, baseEnd_388700] using wordTrace_append hprefix tailTrace_388700
  have hstable : (prefixWord ++ tailWord_388700).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388700).length < 2 ^ (prefixWord ++ tailWord_388700).sum := by decide
  have hdescent : baseEnd_388700 < baseStart_388700 := by decide
  rcases family_descends (prefixWord ++ tailWord_388700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388740 : List Nat := [2, 3, 2, 1, 11]
def baseStart_388740 : Nat := 118140960795 + 388740 * 2 ^ 59
def prefixEnd_388740 : Nat := 4983230072969 + 3 ^ 40 * 388740 * 2
def baseEnd_388740 : Nat := 4381025396519380777223

theorem tailTrace_388740 : CollatzResearch.WordTrace tailWord_388740 prefixEnd_388740 4381025396519380777223 := by
  unfold tailWord_388740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7089256305834423175705837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9452341741112564234274449 7089256305834423175705837)
  ·
    refine ⟨2658471114687908690889689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7089256305834423175705837 2658471114687908690889689)
    ·
      refine ⟨1993853336015931518167267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2658471114687908690889689 1993853336015931518167267)
      ·
        refine ⟨2990780004023897277250901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1993853336015931518167267 2990780004023897277250901)
        ·
          refine ⟨4381025396519380777223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2990780004023897277250901 4381025396519380777223)
          ·
            rfl

theorem cell19_388740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 11].length) (baseStart_388740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388740 prefixEnd_388740 := by exact prefixLift 388740
  have htrace : WordTrace (prefixWord ++ tailWord_388740) baseStart_388740 baseEnd_388740 := by
    simpa [prefixWord, tailWord_388740, baseEnd_388740] using wordTrace_append hprefix tailTrace_388740
  have hstable : (prefixWord ++ tailWord_388740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388740).length < 2 ^ (prefixWord ++ tailWord_388740).sum := by decide
  have hdescent : baseEnd_388740 < baseStart_388740 := by decide
  rcases family_descends (prefixWord ++ tailWord_388740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388797 : List Nat := [1, 4, 1, 2, 1, 2, 8]
def baseStart_388797 : Nat := 118140960795 + 388797 * 2 ^ 59
def prefixEnd_388797 : Nat := 4983230072969 + 3 ^ 40 * 388797 * 2
def baseEnd_388797 : Nat := 39435009980488012572733

theorem tailTrace_388797 : CollatzResearch.WordTrace tailWord_388797 prefixEnd_388797 39435009980488012572733 := by
  unfold tailWord_388797
  simp only [CollatzResearch.WordTrace]
  refine ⟨14180591572462345086236645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9453727714974896724157763 14180591572462345086236645)
  ·
    refine ⟨2658860919836689703669371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14180591572462345086236645 2658860919836689703669371)
    ·
      refine ⟨3988291379755034555504057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2658860919836689703669371 3988291379755034555504057)
      ·
        refine ⟨2991218534816275916628043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3988291379755034555504057 2991218534816275916628043)
        ·
          refine ⟨4486827802224413874942065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991218534816275916628043 4486827802224413874942065)
          ·
            refine ⟨3365120851668310406206549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4486827802224413874942065 3365120851668310406206549)
            ·
              refine ⟨39435009980488012572733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3365120851668310406206549 39435009980488012572733)
              ·
                rfl

theorem cell19_388797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_388797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388797 prefixEnd_388797 := by exact prefixLift 388797
  have htrace : WordTrace (prefixWord ++ tailWord_388797) baseStart_388797 baseEnd_388797 := by
    simpa [prefixWord, tailWord_388797, baseEnd_388797] using wordTrace_append hprefix tailTrace_388797
  have hstable : (prefixWord ++ tailWord_388797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388797).length < 2 ^ (prefixWord ++ tailWord_388797).sum := by decide
  have hdescent : baseEnd_388797 < baseStart_388797 := by decide
  rcases family_descends (prefixWord ++ tailWord_388797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388833 : List Nat := [1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_388833 : Nat := 118140960795 + 388833 * 2 ^ 59
def prefixEnd_388833 : Nat := 4983230072969 + 3 ^ 40 * 388833 * 2
def baseEnd_388833 : Nat := 118315984195426620918101

theorem tailTrace_388833 : CollatzResearch.WordTrace tailWord_388833 prefixEnd_388833 118315984195426620918101 := by
  unfold tailWord_388833
  simp only [CollatzResearch.WordTrace]
  refine ⟨14181904600331923234547153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9454603066887948823031435 14181904600331923234547153)
  ·
    refine ⟨10636428450248942425910365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14181904600331923234547153 10636428450248942425910365)
    ·
      refine ⟨3988660668843353409716387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10636428450248942425910365 3988660668843353409716387)
      ·
        refine ⟨5982991003265030114574581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3988660668843353409716387 5982991003265030114574581)
        ·
          refine ⟨560905406556096573241367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5982991003265030114574581 560905406556096573241367)
          ·
            refine ⟨841358109834144859862051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560905406556096573241367 841358109834144859862051)
            ·
              refine ⟨1262037164751217289793077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841358109834144859862051 1262037164751217289793077)
              ·
                refine ⟨118315984195426620918101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1262037164751217289793077 118315984195426620918101)
                ·
                  rfl

theorem cell19_388833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_388833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388833 prefixEnd_388833 := by exact prefixLift 388833
  have htrace : WordTrace (prefixWord ++ tailWord_388833) baseStart_388833 baseEnd_388833 := by
    simpa [prefixWord, tailWord_388833, baseEnd_388833] using wordTrace_append hprefix tailTrace_388833
  have hstable : (prefixWord ++ tailWord_388833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388833).length < 2 ^ (prefixWord ++ tailWord_388833).sum := by decide
  have hdescent : baseEnd_388833 < baseStart_388833 := by decide
  rcases family_descends (prefixWord ++ tailWord_388833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388892 : List Nat := [2, 2, 3, 1, 1, 2, 1, 7]
def baseStart_388892 : Nat := 118140960795 + 388892 * 2 ^ 59
def prefixEnd_388892 : Nat := 4983230072969 + 3 ^ 40 * 388892 * 2
def baseEnd_388892 : Nat := 118333937000531965606829

theorem tailTrace_388892 : CollatzResearch.WordTrace tailWord_388892 prefixEnd_388892 118333937000531965606829 := by
  unfold tailWord_388892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092028253559088155472465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9456037671412117540629953 7092028253559088155472465)
  ·
    refine ⟨5319021190169316116604349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7092028253559088155472465 5319021190169316116604349)
    ·
      refine ⟨1994632946313493543726631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5319021190169316116604349 1994632946313493543726631)
      ·
        refine ⟨2991949419470240315589947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994632946313493543726631 2991949419470240315589947)
        ·
          refine ⟨4487924129205360473384921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991949419470240315589947 4487924129205360473384921)
          ·
            refine ⟨3365943096904020355038691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4487924129205360473384921 3365943096904020355038691)
            ·
              refine ⟨5048914645356030532558037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365943096904020355038691 5048914645356030532558037)
              ·
                refine ⟨118333937000531965606829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5048914645356030532558037 118333937000531965606829)
                ·
                  rfl

theorem cell19_388892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_388892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388892 prefixEnd_388892 := by exact prefixLift 388892
  have htrace : WordTrace (prefixWord ++ tailWord_388892) baseStart_388892 baseEnd_388892 := by
    simpa [prefixWord, tailWord_388892, baseEnd_388892] using wordTrace_append hprefix tailTrace_388892
  have hstable : (prefixWord ++ tailWord_388892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388892).length < 2 ^ (prefixWord ++ tailWord_388892).sum := by decide
  have hdescent : baseEnd_388892 < baseStart_388892 := by decide
  rcases family_descends (prefixWord ++ tailWord_388892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388926 : List Nat := [4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_388926 : Nat := 118140960795 + 388926 * 2 ^ 59
def prefixEnd_388926 : Nat := 4983230072969 + 3 ^ 40 * 388926 * 2
def baseEnd_388926 : Nat := 118344282684829960851181

theorem tailTrace_388926 : CollatzResearch.WordTrace tailWord_388926 prefixEnd_388926 118344282684829960851181 := by
  unfold tailWord_388926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773162073624375014710329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9456864392663333411788421 1773162073624375014710329)
  ·
    refine ⟨1329871555218281261032747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1773162073624375014710329 1329871555218281261032747)
    ·
      refine ⟨1994807332827421891549121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329871555218281261032747 1994807332827421891549121)
      ·
        refine ⟨1496105499620566418661841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1994807332827421891549121 1496105499620566418661841)
        ·
          refine ⟨1122079124715424813996381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496105499620566418661841 1122079124715424813996381)
          ·
            refine ⟨420779671768284305248643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1122079124715424813996381 420779671768284305248643)
            ·
              refine ⟨631169507652426457872965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420779671768284305248643 631169507652426457872965)
              ·
                refine ⟨118344282684829960851181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 631169507652426457872965 118344282684829960851181)
                ·
                  rfl

theorem cell19_388926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_388926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388926 prefixEnd_388926 := by exact prefixLift 388926
  have htrace : WordTrace (prefixWord ++ tailWord_388926) baseStart_388926 baseEnd_388926 := by
    simpa [prefixWord, tailWord_388926, baseEnd_388926] using wordTrace_append hprefix tailTrace_388926
  have hstable : (prefixWord ++ tailWord_388926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388926).length < 2 ^ (prefixWord ++ tailWord_388926).sum := by decide
  have hdescent : baseEnd_388926 < baseStart_388926 := by decide
  rcases family_descends (prefixWord ++ tailWord_388926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388968 : List Nat := [2, 1, 4, 2, 1, 1, 8]
def baseStart_388968 : Nat := 118140960795 + 388968 * 2 ^ 59
def prefixEnd_388968 : Nat := 4983230072969 + 3 ^ 40 * 388968 * 2
def baseEnd_388968 : Nat := 39452354215928769305911

theorem tailTrace_388968 : CollatzResearch.WordTrace tailWord_388968 prefixEnd_388968 39452354215928769305911 := by
  unfold tailWord_388968
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093414227421420645355779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9457885636561894193807705 7093414227421420645355779)
  ·
    refine ⟨10640121341132130968033669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7093414227421420645355779 10640121341132130968033669)
    ·
      refine ⟨1995022751462274556506313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10640121341132130968033669 1995022751462274556506313)
      ·
        refine ⟨1496267063596705917379735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1995022751462274556506313 1496267063596705917379735)
        ·
          refine ⟨2244400595395058876069603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1496267063596705917379735 2244400595395058876069603)
          ·
            refine ⟨3366600893092588314104405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244400595395058876069603 3366600893092588314104405)
            ·
              refine ⟨39452354215928769305911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3366600893092588314104405 39452354215928769305911)
              ·
                rfl

theorem cell19_388968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_388968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_388968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_388968 prefixEnd_388968 := by exact prefixLift 388968
  have htrace : WordTrace (prefixWord ++ tailWord_388968) baseStart_388968 baseEnd_388968 := by
    simpa [prefixWord, tailWord_388968, baseEnd_388968] using wordTrace_append hprefix tailTrace_388968
  have hstable : (prefixWord ++ tailWord_388968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388968).length < 2 ^ (prefixWord ++ tailWord_388968).sum := by decide
  have hdescent : baseEnd_388968 < baseStart_388968 := by decide
  rcases family_descends (prefixWord ++ tailWord_388968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389000 : List Nat := [2, 1, 3, 3, 4, 1, 2, 3]
def baseStart_389000 : Nat := 118140960795 + 389000 * 2 ^ 59
def prefixEnd_389000 : Nat := 4983230072969 + 3 ^ 40 * 389000 * 2
def baseEnd_389000 : Nat := 118366799762419715206535

theorem tailTrace_389000 : CollatzResearch.WordTrace tailWord_389000 prefixEnd_389000 118366799762419715206535 := by
  unfold tailWord_389000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093997795363455377938227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9458663727151273837250969 7093997795363455377938227)
  ·
    refine ⟨10640996693045183066907341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7093997795363455377938227 10640996693045183066907341)
    ·
      refine ⟨3990373759891943650090253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10640996693045183066907341 3990373759891943650090253)
      ·
        refine ⟨1496390159959478868783845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3990373759891943650090253 1496390159959478868783845)
        ·
          refine ⟨280573154992402287896971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1496390159959478868783845 280573154992402287896971)
          ·
            refine ⟨420859732488603431845457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280573154992402287896971 420859732488603431845457)
            ·
              refine ⟨315644799366452573884093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420859732488603431845457 315644799366452573884093)
              ·
                refine ⟨118366799762419715206535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315644799366452573884093 118366799762419715206535)
                ·
                  rfl

theorem cell19_389000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_389000 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389000 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389000 prefixEnd_389000 := by exact prefixLift 389000
  have htrace : WordTrace (prefixWord ++ tailWord_389000) baseStart_389000 baseEnd_389000 := by
    simpa [prefixWord, tailWord_389000, baseEnd_389000] using wordTrace_append hprefix tailTrace_389000
  have hstable : (prefixWord ++ tailWord_389000).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389000).length < 2 ^ (prefixWord ++ tailWord_389000).sum := by decide
  have hdescent : baseEnd_389000 < baseStart_389000 := by decide
  rcases family_descends (prefixWord ++ tailWord_389000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389023 : List Nat := [1, 1, 2, 5, 3, 2, 5]
def baseStart_389023 : Nat := 118140960795 + 389023 * 2 ^ 59
def prefixEnd_389023 : Nat := 4983230072969 + 3 ^ 40 * 389023 * 2
def baseEnd_389023 : Nat := 39457932771187492231787

theorem tailTrace_389023 : CollatzResearch.WordTrace tailWord_389023 prefixEnd_389023 39457932771187492231787 := by
  unfold tailWord_389023
  simp only [CollatzResearch.WordTrace]
  refine ⟨14188834469643585683963723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9459222979762390455975815 14188834469643585683963723)
  ·
    refine ⟨21283251704465378525945585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14188834469643585683963723 21283251704465378525945585)
    ·
      refine ⟨15962438778349033894459189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21283251704465378525945585 15962438778349033894459189)
      ·
        refine ⟨1496478635470221927605549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15962438778349033894459189 1496478635470221927605549)
        ·
          refine ⟨561179488301333222852081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1496478635470221927605549 561179488301333222852081)
          ·
            refine ⟨420884616225999917139061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561179488301333222852081 420884616225999917139061)
            ·
              refine ⟨39457932771187492231787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 420884616225999917139061 39457932771187492231787)
              ·
                rfl

theorem cell19_389023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_389023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389023 prefixEnd_389023 := by exact prefixLift 389023
  have htrace : WordTrace (prefixWord ++ tailWord_389023) baseStart_389023 baseEnd_389023 := by
    simpa [prefixWord, tailWord_389023, baseEnd_389023] using wordTrace_append hprefix tailTrace_389023
  have hstable : (prefixWord ++ tailWord_389023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389023).length < 2 ^ (prefixWord ++ tailWord_389023).sum := by decide
  have hdescent : baseEnd_389023 < baseStart_389023 := by decide
  rcases family_descends (prefixWord ++ tailWord_389023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389078 : List Nat := [5, 2, 1, 1, 4, 6]
def baseStart_389078 : Nat := 118140960795 + 389078 * 2 ^ 59
def prefixEnd_389078 : Nat := 4983230072969 + 3 ^ 40 * 389078 * 2
def baseEnd_389078 : Nat := 13154503775482071719221

theorem tailTrace_389078 : CollatzResearch.WordTrace tailWord_389078 prefixEnd_389078 13154503775482071719221 := by
  unfold tailWord_389078
  simp only [CollatzResearch.WordTrace]
  refine ⟨886927530277770629825993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9460560322962886718143925 886927530277770629825993)
  ·
    refine ⟨665195647708327972369495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 886927530277770629825993 665195647708327972369495)
    ·
      refine ⟨997793471562491958554243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665195647708327972369495 997793471562491958554243)
      ·
        refine ⟨1496690207343737937831365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997793471562491958554243 1496690207343737937831365)
        ·
          refine ⟨280629413876950863343381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1496690207343737937831365 280629413876950863343381)
          ·
            refine ⟨13154503775482071719221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 280629413876950863343381 13154503775482071719221)
            ·
              rfl

theorem cell19_389078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 6].length) (baseStart_389078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389078 prefixEnd_389078 := by exact prefixLift 389078
  have htrace : WordTrace (prefixWord ++ tailWord_389078) baseStart_389078 baseEnd_389078 := by
    simpa [prefixWord, tailWord_389078, baseEnd_389078] using wordTrace_append hprefix tailTrace_389078
  have hstable : (prefixWord ++ tailWord_389078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389078).length < 2 ^ (prefixWord ++ tailWord_389078).sum := by decide
  have hdescent : baseEnd_389078 < baseStart_389078 := by decide
  rcases family_descends (prefixWord ++ tailWord_389078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389082 : List Nat := [3, 1, 1, 2, 5, 7]
def baseStart_389082 : Nat := 118140960795 + 389082 * 2 ^ 59
def prefixEnd_389082 : Nat := 4983230072969 + 3 ^ 40 * 389082 * 2
def baseEnd_389082 : Nat := 13154639013185313487121

theorem tailTrace_389082 : CollatzResearch.WordTrace tailWord_389082 prefixEnd_389082 13154639013185313487121 := by
  unfold tailWord_389082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547746594107459690090375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9460657584286559173574333 3547746594107459690090375)
  ·
    refine ⟨5321619891161189535135563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3547746594107459690090375 5321619891161189535135563)
    ·
      refine ⟨7982429836741784302703345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5321619891161189535135563 7982429836741784302703345)
      ·
        refine ⟨5986822377556338227027509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7982429836741784302703345 5986822377556338227027509)
        ·
          refine ⟨561264597895906708783829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5986822377556338227027509 561264597895906708783829)
          ·
            refine ⟨13154639013185313487121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 561264597895906708783829 13154639013185313487121)
            ·
              rfl

theorem cell19_389082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_389082 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389082 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389082 prefixEnd_389082 := by exact prefixLift 389082
  have htrace : WordTrace (prefixWord ++ tailWord_389082) baseStart_389082 baseEnd_389082 := by
    simpa [prefixWord, tailWord_389082, baseEnd_389082] using wordTrace_append hprefix tailTrace_389082
  have hstable : (prefixWord ++ tailWord_389082).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389082).length < 2 ^ (prefixWord ++ tailWord_389082).sum := by decide
  have hdescent : baseEnd_389082 < baseStart_389082 := by decide
  rcases family_descends (prefixWord ++ tailWord_389082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389133 : List Nat := [1, 7, 1, 2, 1, 1, 6]
def baseStart_389133 : Nat := 118140960795 + 389133 * 2 ^ 59
def prefixEnd_389133 : Nat := 4983230072969 + 3 ^ 40 * 389133 * 2
def baseEnd_389133 : Nat := 39469089881704938083539

theorem tailTrace_389133 : CollatzResearch.WordTrace tailWord_389133 prefixEnd_389133 39469089881704938083539 := by
  unfold tailWord_389133
  simp only [CollatzResearch.WordTrace]
  refine ⟨14192846499245074470468053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9461897666163382980312035 14192846499245074470468053)
  ·
    refine ⟨332644839826056432901595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14192846499245074470468053 332644839826056432901595)
    ·
      refine ⟨498967259739084649352393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332644839826056432901595 498967259739084649352393)
      ·
        refine ⟨374225444804313487014295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498967259739084649352393 374225444804313487014295)
        ·
          refine ⟨561338167206470230521443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374225444804313487014295 561338167206470230521443)
          ·
            refine ⟨842007250809705345782165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561338167206470230521443 842007250809705345782165)
            ·
              refine ⟨39469089881704938083539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 842007250809705345782165 39469089881704938083539)
              ·
                rfl

theorem cell19_389133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 6].length) (baseStart_389133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389133 prefixEnd_389133 := by exact prefixLift 389133
  have htrace : WordTrace (prefixWord ++ tailWord_389133) baseStart_389133 baseEnd_389133 := by
    simpa [prefixWord, tailWord_389133, baseEnd_389133] using wordTrace_append hprefix tailTrace_389133
  have hstable : (prefixWord ++ tailWord_389133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389133).length < 2 ^ (prefixWord ++ tailWord_389133).sum := by decide
  have hdescent : baseEnd_389133 < baseStart_389133 := by decide
  rcases family_descends (prefixWord ++ tailWord_389133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389179 : List Nat := [1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_389179 : Nat := 118140960795 + 389179 * 2 ^ 59
def prefixEnd_389179 : Nat := 4983230072969 + 3 ^ 40 * 389179 * 2
def baseEnd_389179 : Nat := 118421266747400337228269

theorem tailTrace_389179 : CollatzResearch.WordTrace tailWord_389179 prefixEnd_389179 118421266747400337228269 := by
  unfold tailWord_389179
  simp only [CollatzResearch.WordTrace]
  refine ⟨14194524257078424326642591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9463016171385616217761727 14194524257078424326642591)
  ·
    refine ⟨21291786385617636489963887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14194524257078424326642591 21291786385617636489963887)
    ·
      refine ⟨31937679578426454734945831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21291786385617636489963887 31937679578426454734945831)
      ·
        refine ⟨47906519367639682102418747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31937679578426454734945831 47906519367639682102418747)
        ·
          refine ⟨71859779051459523153628121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47906519367639682102418747 71859779051459523153628121)
          ·
            refine ⟨53894834288594642365221091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71859779051459523153628121 53894834288594642365221091)
            ·
              refine ⟨80842251432891963547831637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53894834288594642365221091 80842251432891963547831637)
              ·
                refine ⟨118421266747400337228269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80842251432891963547831637 118421266747400337228269)
                ·
                  rfl

theorem cell19_389179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_389179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389179 prefixEnd_389179 := by exact prefixLift 389179
  have htrace : WordTrace (prefixWord ++ tailWord_389179) baseStart_389179 baseEnd_389179 := by
    simpa [prefixWord, tailWord_389179, baseEnd_389179] using wordTrace_append hprefix tailTrace_389179
  have hstable : (prefixWord ++ tailWord_389179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389179).length < 2 ^ (prefixWord ++ tailWord_389179).sum := by decide
  have hdescent : baseEnd_389179 < baseStart_389179 := by decide
  rcases family_descends (prefixWord ++ tailWord_389179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389213 : List Nat := [1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_389213 : Nat := 118140960795 + 389213 * 2 ^ 59
def prefixEnd_389213 : Nat := 4983230072969 + 3 ^ 40 * 389213 * 2
def baseEnd_389213 : Nat := 118431612431698332472621

theorem tailTrace_389213 : CollatzResearch.WordTrace tailWord_389213 prefixEnd_389213 118431612431698332472621 := by
  unfold tailWord_389213
  simp only [CollatzResearch.WordTrace]
  refine ⟨14195764338955248133380293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9463842892636832088920195 14195764338955248133380293)
  ·
    refine ⟨2661705813554109025008805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14195764338955248133380293 2661705813554109025008805)
    ·
      refine ⟨499069840041395442189151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2661705813554109025008805 499069840041395442189151)
      ·
        refine ⟨748604760062093163283727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499069840041395442189151 748604760062093163283727)
        ·
          refine ⟨1122907140093139744925591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748604760062093163283727 1122907140093139744925591)
          ·
            refine ⟨1684360710139709617388387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122907140093139744925591 1684360710139709617388387)
            ·
              refine ⟨2526541065209564426082581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684360710139709617388387 2526541065209564426082581)
              ·
                refine ⟨118431612431698332472621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2526541065209564426082581 118431612431698332472621)
                ·
                  rfl

theorem cell19_389213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_389213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389213 prefixEnd_389213 := by exact prefixLift 389213
  have htrace : WordTrace (prefixWord ++ tailWord_389213) baseStart_389213 baseEnd_389213 := by
    simpa [prefixWord, tailWord_389213, baseEnd_389213] using wordTrace_append hprefix tailTrace_389213
  have hstable : (prefixWord ++ tailWord_389213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389213).length < 2 ^ (prefixWord ++ tailWord_389213).sum := by decide
  have hdescent : baseEnd_389213 < baseStart_389213 := by decide
  rcases family_descends (prefixWord ++ tailWord_389213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389234 : List Nat := [3, 2, 1, 2, 2, 2, 2, 5]
def baseStart_389234 : Nat := 118140960795 + 389234 * 2 ^ 59
def prefixEnd_389234 : Nat := 4983230072969 + 3 ^ 40 * 389234 * 2
def baseEnd_389234 : Nat := 118438002413176506005897

theorem tailTrace_389234 : CollatzResearch.WordTrace tailWord_389234 prefixEnd_389234 118438002413176506005897 := by
  unfold tailWord_389234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3549132567969792179973689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9464353514586112479929837 3549132567969792179973689)
  ·
    refine ⟨2661849425977344134980267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3549132567969792179973689 2661849425977344134980267)
    ·
      refine ⟨3992774138966016202470401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2661849425977344134980267 3992774138966016202470401)
      ·
        refine ⟨2994580604224512151852801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3992774138966016202470401 2994580604224512151852801)
        ·
          refine ⟨2245935453168384113889601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2994580604224512151852801 2245935453168384113889601)
          ·
            refine ⟨1684451589876288085417201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2245935453168384113889601 1684451589876288085417201)
            ·
              refine ⟨1263338692407216064062901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1684451589876288085417201 1263338692407216064062901)
              ·
                refine ⟨118438002413176506005897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1263338692407216064062901 118438002413176506005897)
                ·
                  rfl

theorem cell19_389234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_389234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389234 prefixEnd_389234 := by exact prefixLift 389234
  have htrace : WordTrace (prefixWord ++ tailWord_389234) baseStart_389234 baseEnd_389234 := by
    simpa [prefixWord, tailWord_389234, baseEnd_389234] using wordTrace_append hprefix tailTrace_389234
  have hstable : (prefixWord ++ tailWord_389234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389234).length < 2 ^ (prefixWord ++ tailWord_389234).sum := by decide
  have hdescent : baseEnd_389234 < baseStart_389234 := by decide
  rcases family_descends (prefixWord ++ tailWord_389234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389287 : List Nat := [1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_389287 : Nat := 118140960795 + 389287 * 2 ^ 59
def prefixEnd_389287 : Nat := 4983230072969 + 3 ^ 40 * 389287 * 2
def baseEnd_389287 : Nat := 118454129509288086827975

theorem tailTrace_389287 : CollatzResearch.WordTrace tailWord_389287 prefixEnd_389287 118454129509288086827975 := by
  unfold tailWord_389287
  simp only [CollatzResearch.WordTrace]
  refine ⟨14198463340687158771574115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9465642227124772514382743 14198463340687158771574115)
  ·
    refine ⟨21297695011030738157361173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14198463340687158771574115 21297695011030738157361173)
    ·
      refine ⟨998329453642065851126305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21297695011030738157361173 998329453642065851126305)
      ·
        refine ⟨748747090231549388344729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 998329453642065851126305 748747090231549388344729)
        ·
          refine ⟨561560317673662041258547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 748747090231549388344729 561560317673662041258547)
          ·
            refine ⟨842340476510493061887821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561560317673662041258547 842340476510493061887821)
            ·
              refine ⟨315877678691434898207933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842340476510493061887821 315877678691434898207933)
              ·
                refine ⟨118454129509288086827975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315877678691434898207933 118454129509288086827975)
                ·
                  rfl

theorem cell19_389287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_389287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389287 prefixEnd_389287 := by exact prefixLift 389287
  have htrace : WordTrace (prefixWord ++ tailWord_389287) baseStart_389287 baseEnd_389287 := by
    simpa [prefixWord, tailWord_389287, baseEnd_389287] using wordTrace_append hprefix tailTrace_389287
  have hstable : (prefixWord ++ tailWord_389287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389287).length < 2 ^ (prefixWord ++ tailWord_389287).sum := by decide
  have hdescent : baseEnd_389287 < baseStart_389287 := by decide
  rcases family_descends (prefixWord ++ tailWord_389287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389340 : List Nat := [2, 2, 5, 2, 2, 1, 2, 3]
def baseStart_389340 : Nat := 118140960795 + 389340 * 2 ^ 59
def prefixEnd_389340 : Nat := 4983230072969 + 3 ^ 40 * 389340 * 2
def baseEnd_389340 : Nat := 118470256605399667650053

theorem tailTrace_389340 : CollatzResearch.WordTrace tailWord_389340 prefixEnd_389340 118470256605399667650053 := by
  unfold tailWord_389340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7100198204747574411626737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9466930939663432548835649 7100198204747574411626737)
  ·
    refine ⟨5325148653560680808720053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7100198204747574411626737 5325148653560680808720053)
    ·
      refine ⟨499232686271313825817505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5325148653560680808720053 499232686271313825817505)
      ·
        refine ⟨374424514703485369363129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499232686271313825817505 374424514703485369363129)
        ·
          refine ⟨280818386027614027022347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374424514703485369363129 280818386027614027022347)
          ·
            refine ⟨421227579041421040533521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280818386027614027022347 421227579041421040533521)
            ·
              refine ⟨315920684281065780400141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421227579041421040533521 315920684281065780400141)
              ·
                refine ⟨118470256605399667650053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 315920684281065780400141 118470256605399667650053)
                ·
                  rfl

theorem cell19_389340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 3].length) (baseStart_389340 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389340 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389340 prefixEnd_389340 := by exact prefixLift 389340
  have htrace : WordTrace (prefixWord ++ tailWord_389340) baseStart_389340 baseEnd_389340 := by
    simpa [prefixWord, tailWord_389340, baseEnd_389340] using wordTrace_append hprefix tailTrace_389340
  have hstable : (prefixWord ++ tailWord_389340).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389340).length < 2 ^ (prefixWord ++ tailWord_389340).sum := by decide
  have hdescent : baseEnd_389340 < baseStart_389340 := by decide
  rcases family_descends (prefixWord ++ tailWord_389340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389422 : List Nat := [4, 1, 3, 3, 1, 7]
def baseStart_389422 : Nat := 118140960795 + 389422 * 2 ^ 59
def prefixEnd_389422 : Nat := 4983230072969 + 3 ^ 40 * 389422 * 2
def baseEnd_389422 : Nat := 13166134217960863758623

theorem tailTrace_389422 : CollatzResearch.WordTrace tailWord_389422 prefixEnd_389422 13166134217960863758623 := by
  unfold tailWord_389422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775423399399759603467315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9468924796798717885159013 1775423399399759603467315)
  ·
    refine ⟨2663135099099639405200973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1775423399399759603467315 2663135099099639405200973)
    ·
      refine ⟨998675662162364776950365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2663135099099639405200973 998675662162364776950365)
      ·
        refine ⟨374503373310886791356387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 998675662162364776950365 374503373310886791356387)
        ·
          refine ⟨561755059966330187034581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374503373310886791356387 561755059966330187034581)
          ·
            refine ⟨13166134217960863758623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 561755059966330187034581 13166134217960863758623)
            ·
              rfl

theorem cell19_389422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_389422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389422 prefixEnd_389422 := by exact prefixLift 389422
  have htrace : WordTrace (prefixWord ++ tailWord_389422) baseStart_389422 baseEnd_389422 := by
    simpa [prefixWord, tailWord_389422, baseEnd_389422] using wordTrace_append hprefix tailTrace_389422
  have hstable : (prefixWord ++ tailWord_389422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389422).length < 2 ^ (prefixWord ++ tailWord_389422).sum := by decide
  have hdescent : baseEnd_389422 < baseStart_389422 := by decide
  rcases family_descends (prefixWord ++ tailWord_389422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389426 : List Nat := [3, 2, 1, 1, 12]
def baseStart_389426 : Nat := 118140960795 + 389426 * 2 ^ 59
def prefixEnd_389426 : Nat := 4983230072969 + 3 ^ 40 * 389426 * 2
def baseEnd_389426 : Nat := 4388756485221368508841

theorem tailTrace_389426 : CollatzResearch.WordTrace tailWord_389426 prefixEnd_389426 4388756485221368508841 := by
  unfold tailWord_389426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3550883271795896377721033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9469022058122390340589421 3550883271795896377721033)
  ·
    refine ⟨2663162453846922283290775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3550883271795896377721033 2663162453846922283290775)
    ·
      refine ⟨3994743680770383424936163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663162453846922283290775 3994743680770383424936163)
      ·
        refine ⟨5992115521155575137404245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3994743680770383424936163 5992115521155575137404245)
        ·
          refine ⟨4388756485221368508841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5992115521155575137404245 4388756485221368508841)
          ·
            rfl

theorem cell19_389426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 12].length) (baseStart_389426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389426 prefixEnd_389426 := by exact prefixLift 389426
  have htrace : WordTrace (prefixWord ++ tailWord_389426) baseStart_389426 baseEnd_389426 := by
    simpa [prefixWord, tailWord_389426, baseEnd_389426] using wordTrace_append hprefix tailTrace_389426
  have hstable : (prefixWord ++ tailWord_389426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389426).length < 2 ^ (prefixWord ++ tailWord_389426).sum := by decide
  have hdescent : baseEnd_389426 < baseStart_389426 := by decide
  rcases family_descends (prefixWord ++ tailWord_389426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389460 : List Nat := [2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_389460 : Nat := 118140960795 + 389460 * 2 ^ 59
def prefixEnd_389460 : Nat := 4983230072969 + 3 ^ 40 * 389460 * 2
def baseEnd_389460 : Nat := 118506770785274944983059

theorem tailTrace_389460 : CollatzResearch.WordTrace tailWord_389460 prefixEnd_389460 118506770785274944983059 := by
  unfold tailWord_389460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102386584530204658810917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9469848779373606211747889 7102386584530204658810917)
  ·
    refine ⟨1331697484599413373527047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7102386584530204658810917 1331697484599413373527047)
    ·
      refine ⟨1997546226899120060290571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331697484599413373527047 1997546226899120060290571)
      ·
        refine ⟨2996319340348680090435857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1997546226899120060290571 2996319340348680090435857)
        ·
          refine ⟨2247239505261510067826893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2996319340348680090435857 2247239505261510067826893)
          ·
            refine ⟨842714814473066275435085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2247239505261510067826893 842714814473066275435085)
            ·
              refine ⟨316018055427399853288157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842714814473066275435085 316018055427399853288157)
              ·
                refine ⟨118506770785274944983059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316018055427399853288157 118506770785274944983059)
                ·
                  rfl

theorem cell19_389460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_389460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389460 prefixEnd_389460 := by exact prefixLift 389460
  have htrace : WordTrace (prefixWord ++ tailWord_389460) baseStart_389460 baseEnd_389460 := by
    simpa [prefixWord, tailWord_389460, baseEnd_389460] using wordTrace_append hprefix tailTrace_389460
  have hstable : (prefixWord ++ tailWord_389460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389460).length < 2 ^ (prefixWord ++ tailWord_389460).sum := by decide
  have hdescent : baseEnd_389460 < baseStart_389460 := by decide
  rcases family_descends (prefixWord ++ tailWord_389460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389540 : List Nat := [2, 3, 1, 2, 1, 1, 9]
def baseStart_389540 : Nat := 118140960795 + 389540 * 2 ^ 59
def prefixEnd_389540 : Nat := 4983230072969 + 3 ^ 40 * 389540 * 2
def baseEnd_389540 : Nat := 39510371190619487735021

theorem tailTrace_389540 : CollatzResearch.WordTrace tailWord_389540 prefixEnd_389540 39510371190619487735021 := by
  unfold tailWord_389540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103845504385291490267037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9471794005847055320356049 7103845504385291490267037)
  ·
    refine ⟨2663942064144484308850139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7103845504385291490267037 2663942064144484308850139)
    ·
      refine ⟨3995913096216726463275209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663942064144484308850139 3995913096216726463275209)
      ·
        refine ⟨2996934822162544847456407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3995913096216726463275209 2996934822162544847456407)
        ·
          refine ⟨4495402233243817271184611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2996934822162544847456407 4495402233243817271184611)
          ·
            refine ⟨6743103349865725906776917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4495402233243817271184611 6743103349865725906776917)
            ·
              refine ⟨39510371190619487735021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6743103349865725906776917 39510371190619487735021)
              ·
                rfl

theorem cell19_389540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 9].length) (baseStart_389540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389540 prefixEnd_389540 := by exact prefixLift 389540
  have htrace : WordTrace (prefixWord ++ tailWord_389540) baseStart_389540 baseEnd_389540 := by
    simpa [prefixWord, tailWord_389540, baseEnd_389540] using wordTrace_append hprefix tailTrace_389540
  have hstable : (prefixWord ++ tailWord_389540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389540).length < 2 ^ (prefixWord ++ tailWord_389540).sum := by decide
  have hdescent : baseEnd_389540 < baseStart_389540 := by decide
  rcases family_descends (prefixWord ++ tailWord_389540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389559 : List Nat := [1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_389559 : Nat := 118140960795 + 389559 * 2 ^ 59
def prefixEnd_389559 : Nat := 4983230072969 + 3 ^ 40 * 389559 * 2
def baseEnd_389559 : Nat := 118536894983672048782789

theorem tailTrace_389559 : CollatzResearch.WordTrace tailWord_389559 prefixEnd_389559 118536894983672048782789 := by
  unfold tailWord_389559
  simp only [CollatzResearch.WordTrace]
  refine ⟨14208383995701749225475731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9472255997134499483650487 14208383995701749225475731)
  ·
    refine ⟨21312575993552623838213597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14208383995701749225475731 21312575993552623838213597)
    ·
      refine ⟨7992215997582233939330099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21312575993552623838213597 7992215997582233939330099)
      ·
        refine ⟨11988323996373350908995149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7992215997582233939330099 11988323996373350908995149)
        ·
          refine ⟨4495621498640006590873181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11988323996373350908995149 4495621498640006590873181)
          ·
            refine ⟨1685858061990002471577443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4495621498640006590873181 1685858061990002471577443)
            ·
              refine ⟨2528787092985003707366165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685858061990002471577443 2528787092985003707366165)
              ·
                refine ⟨118536894983672048782789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2528787092985003707366165 118536894983672048782789)
                ·
                  rfl

theorem cell19_389559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_389559 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389559 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389559 prefixEnd_389559 := by exact prefixLift 389559
  have htrace : WordTrace (prefixWord ++ tailWord_389559) baseStart_389559 baseEnd_389559 := by
    simpa [prefixWord, tailWord_389559, baseEnd_389559] using wordTrace_append hprefix tailTrace_389559
  have hstable : (prefixWord ++ tailWord_389559).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389559).length < 2 ^ (prefixWord ++ tailWord_389559).sum := by decide
  have hdescent : baseEnd_389559 < baseStart_389559 := by decide
  rcases family_descends (prefixWord ++ tailWord_389559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389578 : List Nat := [3, 1, 2, 1, 2, 2, 1, 7]
def baseStart_389578 : Nat := 118140960795 + 389578 * 2 ^ 59
def prefixEnd_389578 : Nat := 4983230072969 + 3 ^ 40 * 389578 * 2
def baseEnd_389578 : Nat := 118542676395485634360515

theorem tailTrace_389578 : CollatzResearch.WordTrace tailWord_389578 prefixEnd_389578 118542676395485634360515 := by
  unfold tailWord_389578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552269245658228867604347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9472717988421943646944925 3552269245658228867604347)
  ·
    refine ⟨5328403868487343301406521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552269245658228867604347 5328403868487343301406521)
    ·
      refine ⟨3996302901365507476054891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5328403868487343301406521 3996302901365507476054891)
      ·
        refine ⟨5994454352048261214082337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3996302901365507476054891 5994454352048261214082337)
        ·
          refine ⟨4495840764036195910561753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5994454352048261214082337 4495840764036195910561753)
          ·
            refine ⟨3371880573027146932921315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4495840764036195910561753 3371880573027146932921315)
            ·
              refine ⟨5057820859540720399381973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3371880573027146932921315 5057820859540720399381973)
              ·
                refine ⟨118542676395485634360515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5057820859540720399381973 118542676395485634360515)
                ·
                  rfl

theorem cell19_389578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_389578 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389578 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389578 prefixEnd_389578 := by exact prefixLift 389578
  have htrace : WordTrace (prefixWord ++ tailWord_389578) baseStart_389578 baseEnd_389578 := by
    simpa [prefixWord, tailWord_389578, baseEnd_389578] using wordTrace_append hprefix tailTrace_389578
  have hstable : (prefixWord ++ tailWord_389578).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389578).length < 2 ^ (prefixWord ++ tailWord_389578).sum := by decide
  have hdescent : baseEnd_389578 < baseStart_389578 := by decide
  rcases family_descends (prefixWord ++ tailWord_389578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389614 : List Nat := [4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_389614 : Nat := 118140960795 + 389614 * 2 ^ 59
def prefixEnd_389614 : Nat := 4983230072969 + 3 ^ 40 * 389614 * 2
def baseEnd_389614 : Nat := 118553630649448217560417

theorem tailTrace_389614 : CollatzResearch.WordTrace tailWord_389614 prefixEnd_389614 118553630649448217560417 := by
  unfold tailWord_389614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1776298751312811702340987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9473593340334995745818597 1776298751312811702340987)
  ·
    refine ⟨2664448126969217553511481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1776298751312811702340987 2664448126969217553511481)
    ·
      refine ⟨1998336095226913165133611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2664448126969217553511481 1998336095226913165133611)
      ·
        refine ⟨2997504142840369747700417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1998336095226913165133611 2997504142840369747700417)
        ·
          refine ⟨2248128107130277310775313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2997504142840369747700417 2248128107130277310775313)
          ·
            refine ⟨1686096080347707983081485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248128107130277310775313 1686096080347707983081485)
            ·
              refine ⟨632286030130390493655557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1686096080347707983081485 632286030130390493655557)
              ·
                refine ⟨118553630649448217560417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 632286030130390493655557 118553630649448217560417)
                ·
                  rfl

theorem cell19_389614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_389614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389614 prefixEnd_389614 := by exact prefixLift 389614
  have htrace : WordTrace (prefixWord ++ tailWord_389614) baseStart_389614 baseEnd_389614 := by
    simpa [prefixWord, tailWord_389614, baseEnd_389614] using wordTrace_append hprefix tailTrace_389614
  have hstable : (prefixWord ++ tailWord_389614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389614).length < 2 ^ (prefixWord ++ tailWord_389614).sum := by decide
  have hdescent : baseEnd_389614 < baseStart_389614 := by decide
  rcases family_descends (prefixWord ++ tailWord_389614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389684 : List Nat := [2, 5, 1, 3, 1, 2, 2, 3]
def baseStart_389684 : Nat := 118140960795 + 389684 * 2 ^ 59
def prefixEnd_389684 : Nat := 4983230072969 + 3 ^ 40 * 389684 * 2
def baseEnd_389684 : Nat := 118574930587708796004671

theorem tailTrace_389684 : CollatzResearch.WordTrace tailWord_389684 prefixEnd_389684 118574930587708796004671 := by
  unfold tailWord_389684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106471560124447786888053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9475295413499263715850737 7106471560124447786888053)
  ·
    refine ⟨666231708761666980020755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7106471560124447786888053 666231708761666980020755)
    ·
      refine ⟨999347563142500470031133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666231708761666980020755 999347563142500470031133)
      ·
        refine ⟨374755336178437676261675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 999347563142500470031133 374755336178437676261675)
        ·
          refine ⟨562133004267656514392513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374755336178437676261675 562133004267656514392513)
          ·
            refine ⟨421599753200742385794385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562133004267656514392513 421599753200742385794385)
            ·
              refine ⟨316199814900556789345789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421599753200742385794385 316199814900556789345789)
              ·
                refine ⟨118574930587708796004671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316199814900556789345789 118574930587708796004671)
                ·
                  rfl

theorem cell19_389684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2, 3].length) (baseStart_389684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389684 prefixEnd_389684 := by exact prefixLift 389684
  have htrace : WordTrace (prefixWord ++ tailWord_389684) baseStart_389684 baseEnd_389684 := by
    simpa [prefixWord, tailWord_389684, baseEnd_389684] using wordTrace_append hprefix tailTrace_389684
  have hstable : (prefixWord ++ tailWord_389684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389684).length < 2 ^ (prefixWord ++ tailWord_389684).sum := by decide
  have hdescent : baseEnd_389684 < baseStart_389684 := by decide
  rcases family_descends (prefixWord ++ tailWord_389684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389686 : List Nat := [5, 1, 2, 1, 2, 3, 2, 3]
def baseStart_389686 : Nat := 118140960795 + 389686 * 2 ^ 59
def prefixEnd_389686 : Nat := 4983230072969 + 3 ^ 40 * 389686 * 2
def baseEnd_389686 : Nat := 118575539157373383960221

theorem tailTrace_389686 : CollatzResearch.WordTrace tailWord_389686 prefixEnd_389686 118575539157373383960221 := by
  unfold tailWord_389686
  simp only [CollatzResearch.WordTrace]
  refine ⟨888313504140103119709307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9475344044161099943565941 888313504140103119709307)
  ·
    refine ⟨1332470256210154679563961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 888313504140103119709307 1332470256210154679563961)
    ·
      refine ⟨999352692157616009672971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1332470256210154679563961 999352692157616009672971)
      ·
        refine ⟨1499029038236424014509457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999352692157616009672971 1499029038236424014509457)
        ·
          refine ⟨1124271778677318010882093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1499029038236424014509457 1124271778677318010882093)
          ·
            refine ⟨421601917003994254080785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1124271778677318010882093 421601917003994254080785)
            ·
              refine ⟨316201437752995690560589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421601917003994254080785 316201437752995690560589)
              ·
                refine ⟨118575539157373383960221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316201437752995690560589 118575539157373383960221)
                ·
                  rfl

theorem cell19_389686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_389686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389686 prefixEnd_389686 := by exact prefixLift 389686
  have htrace : WordTrace (prefixWord ++ tailWord_389686) baseStart_389686 baseEnd_389686 := by
    simpa [prefixWord, tailWord_389686, baseEnd_389686] using wordTrace_append hprefix tailTrace_389686
  have hstable : (prefixWord ++ tailWord_389686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389686).length < 2 ^ (prefixWord ++ tailWord_389686).sum := by decide
  have hdescent : baseEnd_389686 < baseStart_389686 := by decide
  rcases family_descends (prefixWord ++ tailWord_389686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389690 : List Nat := [3, 1, 1, 1, 3, 3, 4, 3]
def baseStart_389690 : Nat := 118140960795 + 389690 * 2 ^ 59
def prefixEnd_389690 : Nat := 4983230072969 + 3 ^ 40 * 389690 * 2
def baseEnd_389690 : Nat := 118576756296702559871321

theorem tailTrace_389690 : CollatzResearch.WordTrace tailWord_389690 prefixEnd_389690 118576756296702559871321 := by
  unfold tailWord_389690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553290489556789649623631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9475441305484772398996349 3553290489556789649623631)
  ·
    refine ⟨5329935734335184474435447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553290489556789649623631 5329935734335184474435447)
    ·
      refine ⟨7994903601502776711653171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5329935734335184474435447 7994903601502776711653171)
      ·
        refine ⟨11992355402254165067479757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7994903601502776711653171 11992355402254165067479757)
        ·
          refine ⟨4497133275845311900304909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11992355402254165067479757 4497133275845311900304909)
          ·
            refine ⟨1686424978441991962614341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4497133275845311900304909 1686424978441991962614341)
            ·
              refine ⟨316204683457873492990189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1686424978441991962614341 316204683457873492990189)
              ·
                refine ⟨118576756296702559871321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316204683457873492990189 118576756296702559871321)
                ·
                  rfl

theorem cell19_389690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_389690 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389690 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389690 prefixEnd_389690 := by exact prefixLift 389690
  have htrace : WordTrace (prefixWord ++ tailWord_389690) baseStart_389690 baseEnd_389690 := by
    simpa [prefixWord, tailWord_389690, baseEnd_389690] using wordTrace_append hprefix tailTrace_389690
  have hstable : (prefixWord ++ tailWord_389690).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389690).length < 2 ^ (prefixWord ++ tailWord_389690).sum := by decide
  have hdescent : baseEnd_389690 < baseStart_389690 := by decide
  rcases family_descends (prefixWord ++ tailWord_389690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389709 : List Nat := [1, 6, 1, 1, 2, 1, 7]
def baseStart_389709 : Nat := 118140960795 + 389709 * 2 ^ 59
def prefixEnd_389709 : Nat := 4983230072969 + 3 ^ 40 * 389709 * 2
def baseEnd_389709 : Nat := 39527512569505381816349

theorem tailTrace_389709 : CollatzResearch.WordTrace tailWord_389709 prefixEnd_389709 39527512569505381816349 := by
  unfold tailWord_389709
  simp only [CollatzResearch.WordTrace]
  refine ⟨14213854945158324843436181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9475903296772216562290787 14213854945158324843436181)
  ·
    refine ⟨666274450554296477036071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14213854945158324843436181 666274450554296477036071)
    ·
      refine ⟨999411675831444715554107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 666274450554296477036071 999411675831444715554107)
      ·
        refine ⟨1499117513747167073331161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 999411675831444715554107 1499117513747167073331161)
        ·
          refine ⟨1124338135310375304998371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1499117513747167073331161 1124338135310375304998371)
          ·
            refine ⟨1686507202965562957497557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124338135310375304998371 1686507202965562957497557)
            ·
              refine ⟨39527512569505381816349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1686507202965562957497557 39527512569505381816349)
              ·
                rfl

theorem cell19_389709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 7].length) (baseStart_389709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389709 prefixEnd_389709 := by exact prefixLift 389709
  have htrace : WordTrace (prefixWord ++ tailWord_389709) baseStart_389709 baseEnd_389709 := by
    simpa [prefixWord, tailWord_389709, baseEnd_389709] using wordTrace_append hprefix tailTrace_389709
  have hstable : (prefixWord ++ tailWord_389709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389709).length < 2 ^ (prefixWord ++ tailWord_389709).sum := by decide
  have hdescent : baseEnd_389709 < baseStart_389709 := by decide
  rcases family_descends (prefixWord ++ tailWord_389709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389762 : List Nat := [3, 4, 3, 1, 1, 7]
def baseStart_389762 : Nat := 118140960795 + 389762 * 2 ^ 59
def prefixEnd_389762 : Nat := 4983230072969 + 3 ^ 40 * 389762 * 2
def baseEnd_389762 : Nat := 13177629422736414030125

theorem tailTrace_389762 : CollatzResearch.WordTrace tailWord_389762 prefixEnd_389762 13177629422736414030125 := by
  unfold tailWord_389762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553947003491578723778885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9477192009310876596743693 3553947003491578723778885)
  ·
    refine ⟨666365063154671010708541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3553947003491578723778885 666365063154671010708541)
    ·
      refine ⟨249886898683001629015703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 666365063154671010708541 249886898683001629015703)
      ·
        refine ⟨374830348024502443523555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249886898683001629015703 374830348024502443523555)
        ·
          refine ⟨562245522036753665285333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374830348024502443523555 562245522036753665285333)
          ·
            refine ⟨13177629422736414030125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 562245522036753665285333 13177629422736414030125)
            ·
              rfl

theorem cell19_389762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 7].length) (baseStart_389762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389762 prefixEnd_389762 := by exact prefixLift 389762
  have htrace : WordTrace (prefixWord ++ tailWord_389762) baseStart_389762 baseEnd_389762 := by
    simpa [prefixWord, tailWord_389762, baseEnd_389762] using wordTrace_append hprefix tailTrace_389762
  have hstable : (prefixWord ++ tailWord_389762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389762).length < 2 ^ (prefixWord ++ tailWord_389762).sum := by decide
  have hdescent : baseEnd_389762 < baseStart_389762 := by decide
  rcases family_descends (prefixWord ++ tailWord_389762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389859 : List Nat := [1, 1, 1, 7, 1, 3, 2, 3]
def baseStart_389859 : Nat := 118140960795 + 389859 * 2 ^ 59
def prefixEnd_389859 : Nat := 4983230072969 + 3 ^ 40 * 389859 * 2
def baseEnd_389859 : Nat := 118628180433360242115305

theorem tailTrace_389859 : CollatzResearch.WordTrace tailWord_389859 prefixEnd_389859 118628180433360242115305 := by
  unfold tailWord_389859
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219325894614900461396631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9479550596409933640931087 14219325894614900461396631)
  ·
    refine ⟨21328988841922350692094947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14219325894614900461396631 21328988841922350692094947)
    ·
      refine ⟨31993483262883526038142421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21328988841922350692094947 31993483262883526038142421)
      ·
        refine ⟨749847263973832641518963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31993483262883526038142421 749847263973832641518963)
        ·
          refine ⟨1124770895960748962278445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749847263973832641518963 1124770895960748962278445)
          ·
            refine ⟨421789085985280860854417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1124770895960748962278445 421789085985280860854417)
            ·
              refine ⟨316341814488960645640813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421789085985280860854417 316341814488960645640813)
              ·
                refine ⟨118628180433360242115305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316341814488960645640813 118628180433360242115305)
                ·
                  rfl

theorem cell19_389859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_389859 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389859 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389859 prefixEnd_389859 := by exact prefixLift 389859
  have htrace : WordTrace (prefixWord ++ tailWord_389859) baseStart_389859 baseEnd_389859 := by
    simpa [prefixWord, tailWord_389859, baseEnd_389859] using wordTrace_append hprefix tailTrace_389859
  have hstable : (prefixWord ++ tailWord_389859).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389859).length < 2 ^ (prefixWord ++ tailWord_389859).sum := by decide
  have hdescent : baseEnd_389859 < baseStart_389859 := by decide
  rcases family_descends (prefixWord ++ tailWord_389859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389861 : List Nat := [1, 3, 1, 4, 1, 2, 4, 3]
def baseStart_389861 : Nat := 118140960795 + 389861 * 2 ^ 59
def prefixEnd_389861 : Nat := 4983230072969 + 3 ^ 40 * 389861 * 2
def baseEnd_389861 : Nat := 118628789003024830070855

theorem tailTrace_389861 : CollatzResearch.WordTrace tailWord_389861 prefixEnd_389861 118628789003024830070855 := by
  unfold tailWord_389861
  simp only [CollatzResearch.WordTrace]
  refine ⟨14219398840607654802969437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9479599227071769868646291 14219398840607654802969437)
  ·
    refine ⟨5332274565227870551113539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14219398840607654802969437 5332274565227870551113539)
    ·
      refine ⟨7998411847841805826670309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5332274565227870551113539 7998411847841805826670309)
      ·
        refine ⟨1499702221470338592500683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7998411847841805826670309 1499702221470338592500683)
        ·
          refine ⟨2249553332205507888751025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499702221470338592500683 2249553332205507888751025)
          ·
            refine ⟨1687164999154130916563269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2249553332205507888751025 1687164999154130916563269)
            ·
              refine ⟨316343437341399546855613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1687164999154130916563269 316343437341399546855613)
              ·
                refine ⟨118628789003024830070855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316343437341399546855613 118628789003024830070855)
                ·
                  rfl

theorem cell19_389861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 3].length) (baseStart_389861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389861 prefixEnd_389861 := by exact prefixLift 389861
  have htrace : WordTrace (prefixWord ++ tailWord_389861) baseStart_389861 baseEnd_389861 := by
    simpa [prefixWord, tailWord_389861, baseEnd_389861] using wordTrace_append hprefix tailTrace_389861
  have hstable : (prefixWord ++ tailWord_389861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389861).length < 2 ^ (prefixWord ++ tailWord_389861).sum := by decide
  have hdescent : baseEnd_389861 < baseStart_389861 := by decide
  rcases family_descends (prefixWord ++ tailWord_389861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389876 : List Nat := [2, 6, 1, 1, 2, 2, 5]
def baseStart_389876 : Nat := 118140960795 + 389876 * 2 ^ 59
def prefixEnd_389876 : Nat := 4983230072969 + 3 ^ 40 * 389876 * 2
def baseEnd_389876 : Nat := 39544451091836413245827

theorem tailTrace_389876 : CollatzResearch.WordTrace tailWord_389876 prefixEnd_389876 39544451091836413245827 := by
  unfold tailWord_389876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109972967776656182382741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9479963957035541576510321 7109972967776656182382741)
  ·
    refine ⟨333279982864530758549191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7109972967776656182382741 333279982864530758549191)
    ·
      refine ⟨499919974296796137823787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333279982864530758549191 499919974296796137823787)
      ·
        refine ⟨749879961445194206735681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499919974296796137823787 749879961445194206735681)
        ·
          refine ⟨562409971083895655051761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749879961445194206735681 562409971083895655051761)
          ·
            refine ⟨421807478312921741288821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562409971083895655051761 421807478312921741288821)
            ·
              refine ⟨39544451091836413245827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 421807478312921741288821 39544451091836413245827)
              ·
                rfl

theorem cell19_389876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 5].length) (baseStart_389876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389876 prefixEnd_389876 := by exact prefixLift 389876
  have htrace : WordTrace (prefixWord ++ tailWord_389876) baseStart_389876 baseEnd_389876 := by
    simpa [prefixWord, tailWord_389876, baseEnd_389876] using wordTrace_append hprefix tailTrace_389876
  have hstable : (prefixWord ++ tailWord_389876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389876).length < 2 ^ (prefixWord ++ tailWord_389876).sum := by decide
  have hdescent : baseEnd_389876 < baseStart_389876 := by decide
  rcases family_descends (prefixWord ++ tailWord_389876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389920 : List Nat := [2, 1, 1, 5, 1, 2, 2, 5]
def baseStart_389920 : Nat := 118140960795 + 389920 * 2 ^ 59
def prefixEnd_389920 : Nat := 4983230072969 + 3 ^ 40 * 389920 * 2
def baseEnd_389920 : Nat := 118646741808130174759583

theorem tailTrace_389920 : CollatzResearch.WordTrace tailWord_389920 prefixEnd_389920 118646741808130174759583 := by
  unfold tailWord_389920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7110775373696953939683607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9481033831595938586244809 7110775373696953939683607)
  ·
    refine ⟨10666163060545430909525411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7110775373696953939683607 10666163060545430909525411)
    ·
      refine ⟨15999244590818146364288117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10666163060545430909525411 15999244590818146364288117)
      ·
        refine ⟨1499929180389201221652011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15999244590818146364288117 1499929180389201221652011)
        ·
          refine ⟨2249893770583801832478017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499929180389201221652011 2249893770583801832478017)
          ·
            refine ⟨1687420327937851374358513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2249893770583801832478017 1687420327937851374358513)
            ·
              refine ⟨1265565245953388530768885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687420327937851374358513 1265565245953388530768885)
              ·
                refine ⟨118646741808130174759583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1265565245953388530768885 118646741808130174759583)
                ·
                  rfl

theorem cell19_389920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_389920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389920 prefixEnd_389920 := by exact prefixLift 389920
  have htrace : WordTrace (prefixWord ++ tailWord_389920) baseStart_389920 baseEnd_389920 := by
    simpa [prefixWord, tailWord_389920, baseEnd_389920] using wordTrace_append hprefix tailTrace_389920
  have hstable : (prefixWord ++ tailWord_389920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389920).length < 2 ^ (prefixWord ++ tailWord_389920).sum := by decide
  have hdescent : baseEnd_389920 < baseStart_389920 := by decide
  rcases family_descends (prefixWord ++ tailWord_389920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389975 : List Nat := [1, 1, 3, 2, 4, 2, 3, 3]
def baseStart_389975 : Nat := 118140960795 + 389975 * 2 ^ 59
def prefixEnd_389975 : Nat := 4983230072969 + 3 ^ 40 * 389975 * 2
def baseEnd_389975 : Nat := 118663477473906343537211

theorem tailTrace_389975 : CollatzResearch.WordTrace tailWord_389975 prefixEnd_389975 118663477473906343537211 := by
  unfold tailWord_389975
  simp only [CollatzResearch.WordTrace]
  refine ⟨14223556762194652272619379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9482371174796434848412919 14223556762194652272619379)
  ·
    refine ⟨21335335143291978408929069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14223556762194652272619379 21335335143291978408929069)
    ·
      refine ⟨8000750678734491903348401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21335335143291978408929069 8000750678734491903348401)
      ·
        refine ⟨6000563009050868927511301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8000750678734491903348401 6000563009050868927511301)
        ·
          refine ⟨1125105564197037923908369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6000563009050868927511301 1125105564197037923908369)
          ·
            refine ⟨843829173147778442931277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125105564197037923908369 843829173147778442931277)
            ·
              refine ⟨316435939930416916099229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 843829173147778442931277 316435939930416916099229)
              ·
                refine ⟨118663477473906343537211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316435939930416916099229 118663477473906343537211)
                ·
                  rfl

theorem cell19_389975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 3].length) (baseStart_389975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_389975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_389975 prefixEnd_389975 := by exact prefixLift 389975
  have htrace : WordTrace (prefixWord ++ tailWord_389975) baseStart_389975 baseEnd_389975 := by
    simpa [prefixWord, tailWord_389975, baseEnd_389975] using wordTrace_append hprefix tailTrace_389975
  have hstable : (prefixWord ++ tailWord_389975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389975).length < 2 ^ (prefixWord ++ tailWord_389975).sum := by decide
  have hdescent : baseEnd_389975 < baseStart_389975 := by decide
  rcases family_descends (prefixWord ++ tailWord_389975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390068 : List Nat := [2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_390068 : Nat := 118140960795 + 390068 * 2 ^ 59
def prefixEnd_390068 : Nat := 4983230072969 + 3 ^ 40 * 390068 * 2
def baseEnd_390068 : Nat := 118691775963309683470291

theorem tailTrace_390068 : CollatzResearch.WordTrace tailWord_390068 prefixEnd_390068 118691775963309683470291 := by
  unfold tailWord_390068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113474375428864577877429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9484632500571819437169905 7113474375428864577877429)
  ·
    refine ⟨666888222696456054176009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7113474375428864577877429 666888222696456054176009)
    ·
      refine ⟨500166167022342040632007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 666888222696456054176009 500166167022342040632007)
      ·
        refine ⟨750249250533513060948011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500166167022342040632007 750249250533513060948011)
        ·
          refine ⟨1125373875800269591422017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750249250533513060948011 1125373875800269591422017)
          ·
            refine ⟨844030406850202193566513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125373875800269591422017 844030406850202193566513)
            ·
              refine ⟨633022805137651645174885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844030406850202193566513 633022805137651645174885)
              ·
                refine ⟨118691775963309683470291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633022805137651645174885 118691775963309683470291)
                ·
                  rfl

theorem cell19_390068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_390068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390068 prefixEnd_390068 := by exact prefixLift 390068
  have htrace : WordTrace (prefixWord ++ tailWord_390068) baseStart_390068 baseEnd_390068 := by
    simpa [prefixWord, tailWord_390068, baseEnd_390068] using wordTrace_append hprefix tailTrace_390068
  have hstable : (prefixWord ++ tailWord_390068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390068).length < 2 ^ (prefixWord ++ tailWord_390068).sum := by decide
  have hdescent : baseEnd_390068 < baseStart_390068 := by decide
  rcases family_descends (prefixWord ++ tailWord_390068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390072 : List Nat := [2, 1, 2, 1, 2, 5, 2, 4]
def baseStart_390072 : Nat := 118140960795 + 390072 * 2 ^ 59
def prefixEnd_390072 : Nat := 4983230072969 + 3 ^ 40 * 390072 * 2
def baseEnd_390072 : Nat := 118692993102638859381391

theorem tailTrace_390072 : CollatzResearch.WordTrace tailWord_390072 prefixEnd_390072 118692993102638859381391 := by
  unfold tailWord_390072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113547321421618919450235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9484729761895491892600313 7113547321421618919450235)
  ·
    refine ⟨10670320982132428379175353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7113547321421618919450235 10670320982132428379175353)
    ·
      refine ⟨8002740736599321284381515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10670320982132428379175353 8002740736599321284381515)
      ·
        refine ⟨12004111104898981926572273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8002740736599321284381515 12004111104898981926572273)
        ·
          refine ⟨9003083328674236444929205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12004111104898981926572273 9003083328674236444929205)
          ·
            refine ⟨844039062063209666712113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9003083328674236444929205 844039062063209666712113)
            ·
              refine ⟨633029296547407250034085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844039062063209666712113 633029296547407250034085)
              ·
                refine ⟨118692993102638859381391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633029296547407250034085 118692993102638859381391)
                ·
                  rfl

theorem cell19_390072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_390072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390072 prefixEnd_390072 := by exact prefixLift 390072
  have htrace : WordTrace (prefixWord ++ tailWord_390072) baseStart_390072 baseEnd_390072 := by
    simpa [prefixWord, tailWord_390072, baseEnd_390072] using wordTrace_append hprefix tailTrace_390072
  have hstable : (prefixWord ++ tailWord_390072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390072).length < 2 ^ (prefixWord ++ tailWord_390072).sum := by decide
  have hdescent : baseEnd_390072 < baseStart_390072 := by decide
  rcases family_descends (prefixWord ++ tailWord_390072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390129 : List Nat := [1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_390129 : Nat := 118140960795 + 390129 * 2 ^ 59
def prefixEnd_390129 : Nat := 4983230072969 + 3 ^ 40 * 390129 * 2
def baseEnd_390129 : Nat := 118710337338079616114569

theorem tailTrace_390129 : CollatzResearch.WordTrace tailWord_390129 prefixEnd_390129 118710337338079616114569 := by
  unfold tailWord_390129
  simp only [CollatzResearch.WordTrace]
  refine ⟨14229173603636736573725441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9486115735757824382483627 14229173603636736573725441)
  ·
    refine ⟨10671880202727552430294081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14229173603636736573725441 10671880202727552430294081)
    ·
      refine ⟨8003910152045664322720561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10671880202727552430294081 8003910152045664322720561)
      ·
        refine ⟨6002932614034248242040421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8003910152045664322720561 6002932614034248242040421)
        ·
          refine ⟨1125549865131421545382579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6002932614034248242040421 1125549865131421545382579)
          ·
            refine ⟨1688324797697132318073869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1125549865131421545382579 1688324797697132318073869)
            ·
              refine ⟨633121799136424619277701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1688324797697132318073869 633121799136424619277701)
              ·
                refine ⟨118710337338079616114569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633121799136424619277701 118710337338079616114569)
                ·
                  rfl

theorem cell19_390129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_390129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390129 prefixEnd_390129 := by exact prefixLift 390129
  have htrace : WordTrace (prefixWord ++ tailWord_390129) baseStart_390129 baseEnd_390129 := by
    simpa [prefixWord, tailWord_390129, baseEnd_390129] using wordTrace_append hprefix tailTrace_390129
  have hstable : (prefixWord ++ tailWord_390129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390129).length < 2 ^ (prefixWord ++ tailWord_390129).sum := by decide
  have hdescent : baseEnd_390129 < baseStart_390129 := by decide
  rcases family_descends (prefixWord ++ tailWord_390129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390167 : List Nat := [1, 1, 3, 5, 1, 2, 6]
def baseStart_390167 : Nat := 118140960795 + 390167 * 2 ^ 59
def prefixEnd_390167 : Nat := 4983230072969 + 3 ^ 40 * 390167 * 2
def baseEnd_390167 : Nat := 39573966720568929090007

theorem tailTrace_390167 : CollatzResearch.WordTrace tailWord_390167 prefixEnd_390167 39573966720568929090007 := by
  unfold tailWord_390167
  simp only [CollatzResearch.WordTrace]
  refine ⟨14230559577499069063608755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9487039718332712709072503 14230559577499069063608755)
  ·
    refine ⟨21345839366248603595413133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14230559577499069063608755 21345839366248603595413133)
    ·
      refine ⟨8004689762343226348279925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21345839366248603595413133 8004689762343226348279925)
      ·
        refine ⟨750439665219677470151243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8004689762343226348279925 750439665219677470151243)
        ·
          refine ⟨1125659497829516205226865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750439665219677470151243 1125659497829516205226865)
          ·
            refine ⟨844244623372137153920149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125659497829516205226865 844244623372137153920149)
            ·
              refine ⟨39573966720568929090007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 844244623372137153920149 39573966720568929090007)
              ·
                rfl

theorem cell19_390167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_390167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390167 prefixEnd_390167 := by exact prefixLift 390167
  have htrace : WordTrace (prefixWord ++ tailWord_390167) baseStart_390167 baseEnd_390167 := by
    simpa [prefixWord, tailWord_390167, baseEnd_390167] using wordTrace_append hprefix tailTrace_390167
  have hstable : (prefixWord ++ tailWord_390167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390167).length < 2 ^ (prefixWord ++ tailWord_390167).sum := by decide
  have hdescent : baseEnd_390167 < baseStart_390167 := by decide
  rcases family_descends (prefixWord ++ tailWord_390167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390188 : List Nat := [2, 2, 1, 1, 1, 2, 4, 6]
def baseStart_390188 : Nat := 118140960795 + 390188 * 2 ^ 59
def prefixEnd_390188 : Nat := 4983230072969 + 3 ^ 40 * 390188 * 2
def baseEnd_390188 : Nat := 118728290143184960803297

theorem tailTrace_390188 : CollatzResearch.WordTrace tailWord_390188 prefixEnd_390188 118728290143184960803297 := by
  unfold tailWord_390188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115662755211494825061609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9487550340281993100082145 7115662755211494825061609)
  ·
    refine ⟨5336747066408621118796207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7115662755211494825061609 5336747066408621118796207)
    ·
      refine ⟨8005120599612931678194311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5336747066408621118796207 8005120599612931678194311)
      ·
        refine ⟨12007680899419397517291467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8005120599612931678194311 12007680899419397517291467)
        ·
          refine ⟨18011521349129096275937201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12007680899419397517291467 18011521349129096275937201)
          ·
            refine ⟨13508641011846822206952901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18011521349129096275937201 13508641011846822206952901)
            ·
              refine ⟨2532870189721279163803669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13508641011846822206952901 2532870189721279163803669)
              ·
                refine ⟨118728290143184960803297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2532870189721279163803669 118728290143184960803297)
                ·
                  rfl

theorem cell19_390188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_390188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390188 prefixEnd_390188 := by exact prefixLift 390188
  have htrace : WordTrace (prefixWord ++ tailWord_390188) baseStart_390188 baseEnd_390188 := by
    simpa [prefixWord, tailWord_390188, baseEnd_390188] using wordTrace_append hprefix tailTrace_390188
  have hstable : (prefixWord ++ tailWord_390188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390188).length < 2 ^ (prefixWord ++ tailWord_390188).sum := by decide
  have hdescent : baseEnd_390188 < baseStart_390188 := by decide
  rcases family_descends (prefixWord ++ tailWord_390188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390205 : List Nat := [1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_390205 : Nat := 118140960795 + 390205 * 2 ^ 59
def prefixEnd_390205 : Nat := 4983230072969 + 3 ^ 40 * 390205 * 2
def baseEnd_390205 : Nat := 118733462985333958425473

theorem tailTrace_390205 : CollatzResearch.WordTrace tailWord_390205 prefixEnd_390205 118733462985333958425473 := by
  unfold tailWord_390205
  simp only [CollatzResearch.WordTrace]
  refine ⟨14231945551361401553492069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9487963700907601035661379 14231945551361401553492069)
  ·
    refine ⟨2668489790880262791279763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14231945551361401553492069 2668489790880262791279763)
    ·
      refine ⟨4002734686320394186919645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2668489790880262791279763 4002734686320394186919645)
      ·
        refine ⟨1501025507370147820094867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4002734686320394186919645 1501025507370147820094867)
        ·
          refine ⟨2251538261055221730142301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501025507370147820094867 2251538261055221730142301)
          ·
            refine ⟨844326847895708148803363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2251538261055221730142301 844326847895708148803363)
            ·
              refine ⟨1266490271843562223205045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844326847895708148803363 1266490271843562223205045)
              ·
                refine ⟨118733462985333958425473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1266490271843562223205045 118733462985333958425473)
                ·
                  rfl

theorem cell19_390205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_390205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390205 prefixEnd_390205 := by exact prefixLift 390205
  have htrace : WordTrace (prefixWord ++ tailWord_390205) baseStart_390205 baseEnd_390205 := by
    simpa [prefixWord, tailWord_390205, baseEnd_390205] using wordTrace_append hprefix tailTrace_390205
  have hstable : (prefixWord ++ tailWord_390205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390205).length < 2 ^ (prefixWord ++ tailWord_390205).sum := by decide
  have hdescent : baseEnd_390205 < baseStart_390205 := by decide
  rcases family_descends (prefixWord ++ tailWord_390205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390262 : List Nat := [5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_390262 : Nat := 118140960795 + 390262 * 2 ^ 59
def prefixEnd_390262 : Nat := 4983230072969 + 3 ^ 40 * 390262 * 2
def baseEnd_390262 : Nat := 118750807220774715158651

theorem tailTrace_390262 : CollatzResearch.WordTrace tailWord_390262 prefixEnd_390262 118750807220774715158651 := by
  unfold tailWord_390262
  simp only [CollatzResearch.WordTrace]
  refine ⟨889626532009681268019815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9489349674769933525544693 889626532009681268019815)
  ·
    refine ⟨1334439798014521902029723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889626532009681268019815 1334439798014521902029723)
    ·
      refine ⟨2001659697021782853044585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1334439798014521902029723 2001659697021782853044585)
      ·
        refine ⟨1501244772766337139783439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001659697021782853044585 1501244772766337139783439)
        ·
          refine ⟨2251867159149505709675159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501244772766337139783439 2251867159149505709675159)
          ·
            refine ⟨3377800738724258564512739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2251867159149505709675159 3377800738724258564512739)
            ·
              refine ⟨5066701108086387846769109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3377800738724258564512739 5066701108086387846769109)
              ·
                refine ⟨118750807220774715158651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5066701108086387846769109 118750807220774715158651)
                ·
                  rfl

theorem cell19_390262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_390262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390262 prefixEnd_390262 := by exact prefixLift 390262
  have htrace : WordTrace (prefixWord ++ tailWord_390262) baseStart_390262 baseEnd_390262 := by
    simpa [prefixWord, tailWord_390262, baseEnd_390262] using wordTrace_append hprefix tailTrace_390262
  have hstable : (prefixWord ++ tailWord_390262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390262).length < 2 ^ (prefixWord ++ tailWord_390262).sum := by decide
  have hdescent : baseEnd_390262 < baseStart_390262 := by decide
  rcases family_descends (prefixWord ++ tailWord_390262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390264 : List Nat := [2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_390264 : Nat := 118140960795 + 390264 * 2 ^ 59
def prefixEnd_390264 : Nat := 4983230072969 + 3 ^ 40 * 390264 * 2
def baseEnd_390264 : Nat := 118751415790439303114201

theorem tailTrace_390264 : CollatzResearch.WordTrace tailWord_390264 prefixEnd_390264 118751415790439303114201 := by
  unfold tailWord_390264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117048729073827314944923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9489398305431769753259897 7117048729073827314944923)
  ·
    refine ⟨10675573093610740972417385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7117048729073827314944923 10675573093610740972417385)
    ·
      refine ⟨8006679820208055729313039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10675573093610740972417385 8006679820208055729313039)
      ·
        refine ⟨12010019730312083593969559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8006679820208055729313039 12010019730312083593969559)
        ·
          refine ⟨18015029595468125390954339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12010019730312083593969559 18015029595468125390954339)
          ·
            refine ⟨27022544393202188086431509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18015029595468125390954339 27022544393202188086431509)
            ·
              refine ⟨1266681768431352566551477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27022544393202188086431509 1266681768431352566551477)
              ·
                refine ⟨118751415790439303114201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1266681768431352566551477 118751415790439303114201)
                ·
                  rfl

theorem cell19_390264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_390264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390264 prefixEnd_390264 := by exact prefixLift 390264
  have htrace : WordTrace (prefixWord ++ tailWord_390264) baseStart_390264 baseEnd_390264 := by
    simpa [prefixWord, tailWord_390264, baseEnd_390264] using wordTrace_append hprefix tailTrace_390264
  have hstable : (prefixWord ++ tailWord_390264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390264).length < 2 ^ (prefixWord ++ tailWord_390264).sum := by decide
  have hdescent : baseEnd_390264 < baseStart_390264 := by decide
  rcases family_descends (prefixWord ++ tailWord_390264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390298 : List Nat := [3, 1, 1, 5, 1, 3, 1, 4]
def baseStart_390298 : Nat := 118140960795 + 390298 * 2 ^ 59
def prefixEnd_390298 : Nat := 4983230072969 + 3 ^ 40 * 390298 * 2
def baseEnd_390298 : Nat := 118761761474737298358553

theorem tailTrace_390298 : CollatzResearch.WordTrace tailWord_390298 prefixEnd_390298 118761761474737298358553 := by
  unfold tailWord_390298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558834385006119609156887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9490225026682985624418365 3558834385006119609156887)
  ·
    refine ⟨5338251577509179413735331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3558834385006119609156887 5338251577509179413735331)
    ·
      refine ⟨8007377366263769120602997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5338251577509179413735331 8007377366263769120602997)
      ·
        refine ⟨750691628087228355056531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8007377366263769120602997 750691628087228355056531)
        ·
          refine ⟨1126037442130842532584797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750691628087228355056531 1126037442130842532584797)
          ·
            refine ⟨422264040799065949719299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1126037442130842532584797 422264040799065949719299)
            ·
              refine ⟨633396061198598924578949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422264040799065949719299 633396061198598924578949)
              ·
                refine ⟨118761761474737298358553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633396061198598924578949 118761761474737298358553)
                ·
                  rfl

theorem cell19_390298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4].length) (baseStart_390298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390298 prefixEnd_390298 := by exact prefixLift 390298
  have htrace : WordTrace (prefixWord ++ tailWord_390298) baseStart_390298 baseEnd_390298 := by
    simpa [prefixWord, tailWord_390298, baseEnd_390298] using wordTrace_append hprefix tailTrace_390298
  have hstable : (prefixWord ++ tailWord_390298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390298).length < 2 ^ (prefixWord ++ tailWord_390298).sum := by decide
  have hdescent : baseEnd_390298 < baseStart_390298 := by decide
  rcases family_descends (prefixWord ++ tailWord_390298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390300 : List Nat := [2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_390300 : Nat := 118140960795 + 390300 * 2 ^ 59
def prefixEnd_390300 : Nat := 4983230072969 + 3 ^ 40 * 390300 * 2
def baseEnd_390300 : Nat := 118762370044401886314103

theorem tailTrace_390300 : CollatzResearch.WordTrace tailWord_390300 prefixEnd_390300 118762370044401886314103 := by
  unfold tailWord_390300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117705243008616389100177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9490273657344821852133569 7117705243008616389100177)
  ·
    refine ⟨5338278932256462291825133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7117705243008616389100177 5338278932256462291825133)
    ·
      refine ⟨2001854599596173359434425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5338278932256462291825133 2001854599596173359434425)
      ·
        refine ⟨1501390949697130019575819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001854599596173359434425 1501390949697130019575819)
        ·
          refine ⟨2252086424545695029363729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501390949697130019575819 2252086424545695029363729)
          ·
            refine ⟨1689064818409271272022797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2252086424545695029363729 1689064818409271272022797)
            ·
              refine ⟨633399306903476727008549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1689064818409271272022797 633399306903476727008549)
              ·
                refine ⟨118762370044401886314103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633399306903476727008549 118762370044401886314103)
                ·
                  rfl

theorem cell19_390300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_390300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390300 prefixEnd_390300 := by exact prefixLift 390300
  have htrace : WordTrace (prefixWord ++ tailWord_390300) baseStart_390300 baseEnd_390300 := by
    simpa [prefixWord, tailWord_390300, baseEnd_390300] using wordTrace_append hprefix tailTrace_390300
  have hstable : (prefixWord ++ tailWord_390300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390300).length < 2 ^ (prefixWord ++ tailWord_390300).sum := by decide
  have hdescent : baseEnd_390300 < baseStart_390300 := by decide
  rcases family_descends (prefixWord ++ tailWord_390300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390414 : List Nat := [4, 1, 1, 2, 1, 4, 2, 4]
def baseStart_390414 : Nat := 118140960795 + 390414 * 2 ^ 59
def prefixEnd_390414 : Nat := 4983230072969 + 3 ^ 40 * 390414 * 2
def baseEnd_390414 : Nat := 118797058515283399780459

theorem tailTrace_390414 : CollatzResearch.WordTrace tailWord_390414 prefixEnd_390414 118797058515283399780459 := by
  unfold tailWord_390414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779946050950528780981287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9493045605069486831900197 1779946050950528780981287)
  ·
    refine ⟨2669919076425793171471931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779946050950528780981287 2669919076425793171471931)
    ·
      refine ⟨4004878614638689757207897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2669919076425793171471931 4004878614638689757207897)
      ·
        refine ⟨3003658960979017317905923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4004878614638689757207897 3003658960979017317905923)
        ·
          refine ⟨4505488441468525976858885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003658960979017317905923 4505488441468525976858885)
          ·
            refine ⟨844779082775348620661041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4505488441468525976858885 844779082775348620661041)
            ·
              refine ⟨633584312081511465495781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844779082775348620661041 633584312081511465495781)
              ·
                refine ⟨118797058515283399780459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633584312081511465495781 118797058515283399780459)
                ·
                  rfl

theorem cell19_390414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_390414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390414 prefixEnd_390414 := by exact prefixLift 390414
  have htrace : WordTrace (prefixWord ++ tailWord_390414) baseStart_390414 baseEnd_390414 := by
    simpa [prefixWord, tailWord_390414, baseEnd_390414] using wordTrace_append hprefix tailTrace_390414
  have hstable : (prefixWord ++ tailWord_390414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390414).length < 2 ^ (prefixWord ++ tailWord_390414).sum := by decide
  have hdescent : baseEnd_390414 < baseStart_390414 := by decide
  rcases family_descends (prefixWord ++ tailWord_390414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390435 : List Nat := [1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_390435 : Nat := 118140960795 + 390435 * 2 ^ 59
def prefixEnd_390435 : Nat := 4983230072969 + 3 ^ 40 * 390435 * 2
def baseEnd_390435 : Nat := 118803448496761573313735

theorem tailTrace_390435 : CollatzResearch.WordTrace tailWord_390435 prefixEnd_390435 118803448496761573313735 := by
  unfold tailWord_390435
  simp only [CollatzResearch.WordTrace]
  refine ⟨14240334340528150834364759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9493556227018767222909839 14240334340528150834364759)
  ·
    refine ⟨21360501510792226251547139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14240334340528150834364759 21360501510792226251547139)
    ·
      refine ⟨32040752266188339377320709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21360501510792226251547139 32040752266188339377320709)
      ·
        refine ⟨6007641049910313633247633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32040752266188339377320709 6007641049910313633247633)
        ·
          refine ⟨4505730787432735224935725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6007641049910313633247633 4505730787432735224935725)
          ·
            refine ⟨1689649045287275709350897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4505730787432735224935725 1689649045287275709350897)
            ·
              refine ⟨1267236783965456782013173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1689649045287275709350897 1267236783965456782013173)
              ·
                refine ⟨118803448496761573313735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1267236783965456782013173 118803448496761573313735)
                ·
                  rfl

theorem cell19_390435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_390435 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390435 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390435 prefixEnd_390435 := by exact prefixLift 390435
  have htrace : WordTrace (prefixWord ++ tailWord_390435) baseStart_390435 baseEnd_390435 := by
    simpa [prefixWord, tailWord_390435, baseEnd_390435] using wordTrace_append hprefix tailTrace_390435
  have hstable : (prefixWord ++ tailWord_390435).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390435).length < 2 ^ (prefixWord ++ tailWord_390435).sum := by decide
  have hdescent : baseEnd_390435 < baseStart_390435 := by decide
  rcases family_descends (prefixWord ++ tailWord_390435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390471 : List Nat := [1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_390471 : Nat := 118140960795 + 390471 * 2 ^ 59
def prefixEnd_390471 : Nat := 4983230072969 + 3 ^ 40 * 390471 * 2
def baseEnd_390471 : Nat := 118814402750724156513637

theorem tailTrace_390471 : CollatzResearch.WordTrace tailWord_390471 prefixEnd_390471 118814402750724156513637 := by
  unfold tailWord_390471
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241647368397728982675267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9494431578931819321783511 14241647368397728982675267)
  ·
    refine ⟨21362471052596593474012901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14241647368397728982675267 21362471052596593474012901)
    ·
      refine ⟨4005463322361861276377419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21362471052596593474012901 4005463322361861276377419)
      ·
        refine ⟨6008194983542791914566129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4005463322361861276377419 6008194983542791914566129)
        ·
          refine ⟨4506146237657093935924597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6008194983542791914566129 4506146237657093935924597)
          ·
            refine ⟨422451209780352556492931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4506146237657093935924597 422451209780352556492931)
            ·
              refine ⟨633676814670528834739397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422451209780352556492931 633676814670528834739397)
              ·
                refine ⟨118814402750724156513637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633676814670528834739397 118814402750724156513637)
                ·
                  rfl

theorem cell19_390471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_390471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390471 prefixEnd_390471 := by exact prefixLift 390471
  have htrace : WordTrace (prefixWord ++ tailWord_390471) baseStart_390471 baseEnd_390471 := by
    simpa [prefixWord, tailWord_390471, baseEnd_390471] using wordTrace_append hprefix tailTrace_390471
  have hstable : (prefixWord ++ tailWord_390471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390471).length < 2 ^ (prefixWord ++ tailWord_390471).sum := by decide
  have hdescent : baseEnd_390471 < baseStart_390471 := by decide
  rcases family_descends (prefixWord ++ tailWord_390471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390473 : List Nat := [1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_390473 : Nat := 118140960795 + 390473 * 2 ^ 59
def prefixEnd_390473 : Nat := 4983230072969 + 3 ^ 40 * 390473 * 2
def baseEnd_390473 : Nat := 118815011320388744469187

theorem tailTrace_390473 : CollatzResearch.WordTrace tailWord_390473 prefixEnd_390473 118815011320388744469187 := by
  unfold tailWord_390473
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241720314390483324248073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9494480209593655549498715 14241720314390483324248073)
  ·
    refine ⟨10681290235792862493186055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14241720314390483324248073 10681290235792862493186055)
    ·
      refine ⟨16021935353689293739779083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10681290235792862493186055 16021935353689293739779083)
      ·
        refine ⟨24032903030533940609668625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16021935353689293739779083 24032903030533940609668625)
        ·
          refine ⟨18024677272900455457251469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24032903030533940609668625 18024677272900455457251469)
          ·
            refine ⟨6759253977337670796469301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18024677272900455457251469 6759253977337670796469301)
            ·
              refine ⟨633680060375406637168997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6759253977337670796469301 633680060375406637168997)
              ·
                refine ⟨118815011320388744469187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633680060375406637168997 118815011320388744469187)
                ·
                  rfl

theorem cell19_390473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_390473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390473 prefixEnd_390473 := by exact prefixLift 390473
  have htrace : WordTrace (prefixWord ++ tailWord_390473) baseStart_390473 baseEnd_390473 := by
    simpa [prefixWord, tailWord_390473, baseEnd_390473] using wordTrace_append hprefix tailTrace_390473
  have hstable : (prefixWord ++ tailWord_390473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390473).length < 2 ^ (prefixWord ++ tailWord_390473).sum := by decide
  have hdescent : baseEnd_390473 < baseStart_390473 := by decide
  rcases family_descends (prefixWord ++ tailWord_390473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390585 : List Nat := [1, 2, 1, 4, 4, 1, 2, 4]
def baseStart_390585 : Nat := 118140960795 + 390585 * 2 ^ 59
def prefixEnd_390585 : Nat := 4983230072969 + 3 ^ 40 * 390585 * 2
def baseEnd_390585 : Nat := 118849091221605669979993

theorem tailTrace_390585 : CollatzResearch.WordTrace tailWord_390585 prefixEnd_390585 118849091221605669979993 := by
  unfold tailWord_390585
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245805289984726452325209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9497203526656484301550139 14245805289984726452325209)
  ·
    refine ⟨10684353967488544839243907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14245805289984726452325209 10684353967488544839243907)
    ·
      refine ⟨16026530951232817258865861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10684353967488544839243907 16026530951232817258865861)
      ·
        refine ⟨3004974553356153236037349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16026530951232817258865861 3004974553356153236037349)
        ·
          refine ⟨563432728754278731757003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3004974553356153236037349 563432728754278731757003)
          ·
            refine ⟨845149093131418097635505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563432728754278731757003 845149093131418097635505)
            ·
              refine ⟨633861819848563573226629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845149093131418097635505 633861819848563573226629)
              ·
                refine ⟨118849091221605669979993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633861819848563573226629 118849091221605669979993)
                ·
                  rfl

theorem cell19_390585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4].length) (baseStart_390585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390585 prefixEnd_390585 := by exact prefixLift 390585
  have htrace : WordTrace (prefixWord ++ tailWord_390585) baseStart_390585 baseEnd_390585 := by
    simpa [prefixWord, tailWord_390585, baseEnd_390585] using wordTrace_append hprefix tailTrace_390585
  have hstable : (prefixWord ++ tailWord_390585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390585).length < 2 ^ (prefixWord ++ tailWord_390585).sum := by decide
  have hdescent : baseEnd_390585 < baseStart_390585 := by decide
  rcases family_descends (prefixWord ++ tailWord_390585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390606 : List Nat := [4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_390606 : Nat := 118140960795 + 390606 * 2 ^ 59
def prefixEnd_390606 : Nat := 4983230072969 + 3 ^ 40 * 390606 * 2
def baseEnd_390606 : Nat := 118855481203083843513269

theorem tailTrace_390606 : CollatzResearch.WordTrace tailWord_390606 prefixEnd_390606 118855481203083843513269 := by
  unfold tailWord_390606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780821402863580879854959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9497714148605764692559781 1780821402863580879854959)
  ·
    refine ⟨2671232104295371319782439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1780821402863580879854959 2671232104295371319782439)
    ·
      refine ⟨4006848156443056979673659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671232104295371319782439 4006848156443056979673659)
      ·
        refine ⟨6010272234664585469510489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4006848156443056979673659 6010272234664585469510489)
        ·
          refine ⟨4507704175998439102132867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6010272234664585469510489 4507704175998439102132867)
          ·
            refine ⟨6761556263997658653199301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4507704175998439102132867 6761556263997658653199301)
            ·
              refine ⟨1267791799499560997474869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6761556263997658653199301 1267791799499560997474869)
              ·
                refine ⟨118855481203083843513269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1267791799499560997474869 118855481203083843513269)
                ·
                  rfl

theorem cell19_390606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_390606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390606 prefixEnd_390606 := by exact prefixLift 390606
  have htrace : WordTrace (prefixWord ++ tailWord_390606) baseStart_390606 baseEnd_390606 := by
    simpa [prefixWord, tailWord_390606, baseEnd_390606] using wordTrace_append hprefix tailTrace_390606
  have hstable : (prefixWord ++ tailWord_390606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390606).length < 2 ^ (prefixWord ++ tailWord_390606).sum := by decide
  have hdescent : baseEnd_390606 < baseStart_390606 := by decide
  rcases family_descends (prefixWord ++ tailWord_390606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390642 : List Nat := [3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_390642 : Nat := 118140960795 + 390642 * 2 ^ 59
def prefixEnd_390642 : Nat := 4983230072969 + 3 ^ 40 * 390642 * 2
def baseEnd_390642 : Nat := 118866435457046426713171

theorem tailTrace_390642 : CollatzResearch.WordTrace tailWord_390642 prefixEnd_390642 118866435457046426713171 := by
  unfold tailWord_390642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3561971062694556296787545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9498589500518816791433453 3561971062694556296787545)
  ·
    refine ⟨2671478297020917222590659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3561971062694556296787545 2671478297020917222590659)
    ·
      refine ⟨4007217445531375833885989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671478297020917222590659 4007217445531375833885989)
      ·
        refine ⟨751353271037132968853623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4007217445531375833885989 751353271037132968853623)
        ·
          refine ⟨1127029906555699453280435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751353271037132968853623 1127029906555699453280435)
          ·
            refine ⟨1690544859833549179920653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127029906555699453280435 1690544859833549179920653)
            ·
              refine ⟨633954322437580942470245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690544859833549179920653 633954322437580942470245)
              ·
                refine ⟨118866435457046426713171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 633954322437580942470245 118866435457046426713171)
                ·
                  rfl

theorem cell19_390642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_390642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390642 prefixEnd_390642 := by exact prefixLift 390642
  have htrace : WordTrace (prefixWord ++ tailWord_390642) baseStart_390642 baseEnd_390642 := by
    simpa [prefixWord, tailWord_390642, baseEnd_390642] using wordTrace_append hprefix tailTrace_390642
  have hstable : (prefixWord ++ tailWord_390642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390642).length < 2 ^ (prefixWord ++ tailWord_390642).sum := by decide
  have hdescent : baseEnd_390642 < baseStart_390642 := by decide
  rcases family_descends (prefixWord ++ tailWord_390642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390716 : List Nat := [2, 2, 2, 2, 4, 2, 2, 3]
def baseStart_390716 : Nat := 118140960795 + 390716 * 2 ^ 59
def prefixEnd_390716 : Nat := 4983230072969 + 3 ^ 40 * 390716 * 2
def baseEnd_390716 : Nat := 118888952534636181068525

theorem tailTrace_390716 : CollatzResearch.WordTrace tailWord_390716 prefixEnd_390716 118888952534636181068525 := by
  unfold tailWord_390716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125291626255067912672001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9500388835006757216896001 7125291626255067912672001)
  ·
    refine ⟨5343968719691300934504001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7125291626255067912672001 5343968719691300934504001)
    ·
      refine ⟨4007976539768475700878001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5343968719691300934504001 4007976539768475700878001)
      ·
        refine ⟨3005982404826356775658501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007976539768475700878001 3005982404826356775658501)
        ·
          refine ⟨563621700904941895435969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3005982404826356775658501 563621700904941895435969)
          ·
            refine ⟨422716275678706421576977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563621700904941895435969 422716275678706421576977)
            ·
              refine ⟨317037206759029816182733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422716275678706421576977 317037206759029816182733)
              ·
                refine ⟨118888952534636181068525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317037206759029816182733 118888952534636181068525)
                ·
                  rfl

theorem cell19_390716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_390716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390716 prefixEnd_390716 := by exact prefixLift 390716
  have htrace : WordTrace (prefixWord ++ tailWord_390716) baseStart_390716 baseEnd_390716 := by
    simpa [prefixWord, tailWord_390716, baseEnd_390716] using wordTrace_append hprefix tailTrace_390716
  have hstable : (prefixWord ++ tailWord_390716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390716).length < 2 ^ (prefixWord ++ tailWord_390716).sum := by decide
  have hdescent : baseEnd_390716 < baseStart_390716 := by decide
  rcases family_descends (prefixWord ++ tailWord_390716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390779 : List Nat := [1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_390779 : Nat := 118140960795 + 390779 * 2 ^ 59
def prefixEnd_390779 : Nat := 4983230072969 + 3 ^ 40 * 390779 * 2
def baseEnd_390779 : Nat := 118908122479070701668353

theorem tailTrace_390779 : CollatzResearch.WordTrace tailWord_390779 prefixEnd_390779 118908122479070701668353 := by
  unfold tailWord_390779
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252881051281897584887391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9501920700854598389924927 14252881051281897584887391)
  ·
    refine ⟨21379321576922846377331087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14252881051281897584887391 21379321576922846377331087)
    ·
      refine ⟨32068982365384269565996631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21379321576922846377331087 32068982365384269565996631)
      ·
        refine ⟨48103473548076404348994947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32068982365384269565996631 48103473548076404348994947)
        ·
          refine ⟨72155210322114606523492421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48103473548076404348994947 72155210322114606523492421)
          ·
            refine ⟨13529101935396488723154829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72155210322114606523492421 13529101935396488723154829)
            ·
              refine ⟨5073413225773683271183061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13529101935396488723154829 5073413225773683271183061)
              ·
                refine ⟨118908122479070701668353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5073413225773683271183061 118908122479070701668353)
                ·
                  rfl

theorem cell19_390779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_390779 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390779 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390779 prefixEnd_390779 := by exact prefixLift 390779
  have htrace : WordTrace (prefixWord ++ tailWord_390779) baseStart_390779 baseEnd_390779 := by
    simpa [prefixWord, tailWord_390779, baseEnd_390779] using wordTrace_append hprefix tailTrace_390779
  have hstable : (prefixWord ++ tailWord_390779).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390779).length < 2 ^ (prefixWord ++ tailWord_390779).sum := by decide
  have hdescent : baseEnd_390779 < baseStart_390779 := by decide
  rcases family_descends (prefixWord ++ tailWord_390779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390855 : List Nat := [1, 1, 4, 1, 1, 1, 10]
def baseStart_390855 : Nat := 118140960795 + 390855 * 2 ^ 59
def prefixEnd_390855 : Nat := 4983230072969 + 3 ^ 40 * 390855 * 2
def baseEnd_390855 : Nat := 39643749375441681326419

theorem tailTrace_390855 : CollatzResearch.WordTrace tailWord_390855 prefixEnd_390855 39643749375441681326419 := by
  unfold tailWord_390855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14255652999006562564654019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9503768666004375043102679 14255652999006562564654019)
  ·
    refine ⟨21383479498509843846981029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14255652999006562564654019 21383479498509843846981029)
    ·
      refine ⟨4009402405970595721308943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21383479498509843846981029 4009402405970595721308943)
      ·
        refine ⟨6014103608955893581963415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4009402405970595721308943 6014103608955893581963415)
        ·
          refine ⟨9021155413433840372945123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6014103608955893581963415 9021155413433840372945123)
          ·
            refine ⟨13531733120150760559417685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9021155413433840372945123 13531733120150760559417685)
            ·
              refine ⟨39643749375441681326419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13531733120150760559417685 39643749375441681326419)
              ·
                rfl

theorem cell19_390855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_390855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390855 prefixEnd_390855 := by exact prefixLift 390855
  have htrace : WordTrace (prefixWord ++ tailWord_390855) baseStart_390855 baseEnd_390855 := by
    simpa [prefixWord, tailWord_390855, baseEnd_390855] using wordTrace_append hprefix tailTrace_390855
  have hstable : (prefixWord ++ tailWord_390855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390855).length < 2 ^ (prefixWord ++ tailWord_390855).sum := by decide
  have hdescent : baseEnd_390855 < baseStart_390855 := by decide
  rcases family_descends (prefixWord ++ tailWord_390855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390891 : List Nat := [1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_390891 : Nat := 118140960795 + 390891 * 2 ^ 59
def prefixEnd_390891 : Nat := 4983230072969 + 3 ^ 40 * 390891 * 2
def baseEnd_390891 : Nat := 118942202380287627179159

theorem tailTrace_390891 : CollatzResearch.WordTrace tailWord_390891 prefixEnd_390891 118942202380287627179159 := by
  unfold tailWord_390891
  simp only [CollatzResearch.WordTrace]
  refine ⟨14256966026876140712964527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9504644017917427141976351 14256966026876140712964527)
  ·
    refine ⟨21385449040314211069446791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14256966026876140712964527 21385449040314211069446791)
    ·
      refine ⟨32078173560471316604170187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21385449040314211069446791 32078173560471316604170187)
      ·
        refine ⟨48117260340706974906255281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32078173560471316604170187 48117260340706974906255281)
        ·
          refine ⟨36087945255530231179691461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48117260340706974906255281 36087945255530231179691461)
          ·
            refine ⟨6766489735411918346192149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36087945255530231179691461 6766489735411918346192149)
            ·
              refine ⟨317179206347433672477757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6766489735411918346192149 317179206347433672477757)
              ·
                refine ⟨118942202380287627179159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317179206347433672477757 118942202380287627179159)
                ·
                  rfl

theorem cell19_390891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_390891 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390891 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390891 prefixEnd_390891 := by exact prefixLift 390891
  have htrace : WordTrace (prefixWord ++ tailWord_390891) baseStart_390891 baseEnd_390891 := by
    simpa [prefixWord, tailWord_390891, baseEnd_390891] using wordTrace_append hprefix tailTrace_390891
  have hstable : (prefixWord ++ tailWord_390891).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390891).length < 2 ^ (prefixWord ++ tailWord_390891).sum := by decide
  have hdescent : baseEnd_390891 < baseStart_390891 := by decide
  rcases family_descends (prefixWord ++ tailWord_390891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390948 : List Nat := [2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_390948 : Nat := 118140960795 + 390948 * 2 ^ 59
def prefixEnd_390948 : Nat := 4983230072969 + 3 ^ 40 * 390948 * 2
def baseEnd_390948 : Nat := 118959546615728383912337

theorem tailTrace_390948 : CollatzResearch.WordTrace tailWord_390948 prefixEnd_390948 118959546615728383912337 := by
  unfold tailWord_390948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7129522493834819723894749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9506029991779759631859665 7129522493834819723894749)
  ·
    refine ⟨2673570935188057396460531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7129522493834819723894749 2673570935188057396460531)
    ·
      refine ⟨4010356402782086094690797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673570935188057396460531 4010356402782086094690797)
      ·
        refine ⟨1503883651043282285509049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4010356402782086094690797 1503883651043282285509049)
        ·
          refine ⟨1127912738282461714131787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503883651043282285509049 1127912738282461714131787)
          ·
            refine ⟨1691869107423692571197681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127912738282461714131787 1691869107423692571197681)
            ·
              refine ⟨1268901830567769428398261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691869107423692571197681 1268901830567769428398261)
              ·
                refine ⟨118959546615728383912337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1268901830567769428398261 118959546615728383912337)
                ·
                  rfl

theorem cell19_390948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_390948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390948 prefixEnd_390948 := by exact prefixLift 390948
  have htrace : WordTrace (prefixWord ++ tailWord_390948) baseStart_390948 baseEnd_390948 := by
    simpa [prefixWord, tailWord_390948, baseEnd_390948] using wordTrace_append hprefix tailTrace_390948
  have hstable : (prefixWord ++ tailWord_390948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390948).length < 2 ^ (prefixWord ++ tailWord_390948).sum := by decide
  have hdescent : baseEnd_390948 < baseStart_390948 := by decide
  rcases family_descends (prefixWord ++ tailWord_390948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390982 : List Nat := [6, 1, 1, 2, 1, 1, 3, 4]
def baseStart_390982 : Nat := 118140960795 + 390982 * 2 ^ 59
def prefixEnd_390982 : Nat := 4983230072969 + 3 ^ 40 * 390982 * 2
def baseEnd_390982 : Nat := 118969892300026379156689

theorem tailTrace_390982 : CollatzResearch.WordTrace tailWord_390982 prefixEnd_390982 118969892300026379156689 := by
  unfold tailWord_390982
  simp only [CollatzResearch.WordTrace]
  refine ⟨445633908423326976703975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9506856713030975503018133 445633908423326976703975)
  ·
    refine ⟨668450862634990465055963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 445633908423326976703975 668450862634990465055963)
    ·
      refine ⟨1002676293952485697583945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668450862634990465055963 1002676293952485697583945)
      ·
        refine ⟨752007220464364273187959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1002676293952485697583945 752007220464364273187959)
        ·
          refine ⟨1128010830696546409781939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752007220464364273187959 1128010830696546409781939)
          ·
            refine ⟨1692016246044819614672909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128010830696546409781939 1692016246044819614672909)
            ·
              refine ⟨634506092266807355502341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1692016246044819614672909 634506092266807355502341)
              ·
                refine ⟨118969892300026379156689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 634506092266807355502341 118969892300026379156689)
                ·
                  rfl

theorem cell19_390982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_390982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_390982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_390982 prefixEnd_390982 := by exact prefixLift 390982
  have htrace : WordTrace (prefixWord ++ tailWord_390982) baseStart_390982 baseEnd_390982 := by
    simpa [prefixWord, tailWord_390982, baseEnd_390982] using wordTrace_append hprefix tailTrace_390982
  have hstable : (prefixWord ++ tailWord_390982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390982).length < 2 ^ (prefixWord ++ tailWord_390982).sum := by decide
  have hdescent : baseEnd_390982 < baseStart_390982 := by decide
  rcases family_descends (prefixWord ++ tailWord_390982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391045 : List Nat := [1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_391045 : Nat := 118140960795 + 391045 * 2 ^ 59
def prefixEnd_391045 : Nat := 4983230072969 + 3 ^ 40 * 391045 * 2
def baseEnd_391045 : Nat := 118989062244460899756517

theorem tailTrace_391045 : CollatzResearch.WordTrace tailWord_391045 prefixEnd_391045 118989062244460899756517 := by
  unfold tailWord_391045
  simp only [CollatzResearch.WordTrace]
  refine ⟨14262582868318225014070589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9508388578878816676047059 14262582868318225014070589)
  ·
    refine ⟨5348468575619334380276471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14262582868318225014070589 5348468575619334380276471)
    ·
      refine ⟨8022702863429001570414707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348468575619334380276471 8022702863429001570414707)
      ·
        refine ⟨12034054295143502355622061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8022702863429001570414707 12034054295143502355622061)
        ·
          refine ⟨4512770360678813383358273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12034054295143502355622061 4512770360678813383358273)
          ·
            refine ⟨3384577770509110037518705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4512770360678813383358273 3384577770509110037518705)
            ·
              refine ⟨2538433327881832528139029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3384577770509110037518705 2538433327881832528139029)
              ·
                refine ⟨118989062244460899756517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2538433327881832528139029 118989062244460899756517)
                ·
                  rfl

theorem cell19_391045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_391045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391045 prefixEnd_391045 := by exact prefixLift 391045
  have htrace : WordTrace (prefixWord ++ tailWord_391045) baseStart_391045 baseEnd_391045 := by
    simpa [prefixWord, tailWord_391045, baseEnd_391045] using wordTrace_append hprefix tailTrace_391045
  have hstable : (prefixWord ++ tailWord_391045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391045).length < 2 ^ (prefixWord ++ tailWord_391045).sum := by decide
  have hdescent : baseEnd_391045 < baseStart_391045 := by decide
  rcases family_descends (prefixWord ++ tailWord_391045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391058 : List Nat := [3, 2, 3, 2, 1, 3, 2, 3]
def baseStart_391058 : Nat := 118140960795 + 391058 * 2 ^ 59
def prefixEnd_391058 : Nat := 4983230072969 + 3 ^ 40 * 391058 * 2
def baseEnd_391058 : Nat := 118993017947280721467593

theorem tailTrace_391058 : CollatzResearch.WordTrace tailWord_391058 prefixEnd_391058 118993017947280721467593 := by
  unfold tailWord_391058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3565764254317782058573457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9508704678180752156195885 3565764254317782058573457)
  ·
    refine ⟨2674323190738336543930093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3565764254317782058573457 2674323190738336543930093)
    ·
      refine ⟨1002871196526876203973785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2674323190738336543930093 1002871196526876203973785)
      ·
        refine ⟨752153397395157152980339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1002871196526876203973785 752153397395157152980339)
        ·
          refine ⟨1128230096092735729470509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752153397395157152980339 1128230096092735729470509)
          ·
            refine ⟨423086286034775898551441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1128230096092735729470509 423086286034775898551441)
            ·
              refine ⟨317314714526081923913581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423086286034775898551441 317314714526081923913581)
              ·
                refine ⟨118993017947280721467593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317314714526081923913581 118993017947280721467593)
                ·
                  rfl

theorem cell19_391058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_391058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391058 prefixEnd_391058 := by exact prefixLift 391058
  have htrace : WordTrace (prefixWord ++ tailWord_391058) baseStart_391058 baseEnd_391058 := by
    simpa [prefixWord, tailWord_391058, baseEnd_391058] using wordTrace_append hprefix tailTrace_391058
  have hstable : (prefixWord ++ tailWord_391058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391058).length < 2 ^ (prefixWord ++ tailWord_391058).sum := by decide
  have hdescent : baseEnd_391058 < baseStart_391058 := by decide
  rcases family_descends (prefixWord ++ tailWord_391058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391060 : List Nat := [2, 4, 2, 1, 1, 2, 4, 3]
def baseStart_391060 : Nat := 118140960795 + 391060 * 2 ^ 59
def prefixEnd_391060 : Nat := 4983230072969 + 3 ^ 40 * 391060 * 2
def baseEnd_391060 : Nat := 118993626516945309423143

theorem tailTrace_391060 : CollatzResearch.WordTrace tailWord_391060 prefixEnd_391060 118993626516945309423143 := by
  unfold tailWord_391060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7131564981631941287933317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9508753308842588383911089 7131564981631941287933317)
  ·
    refine ⟨1337168434055988991487497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7131564981631941287933317 1337168434055988991487497)
    ·
      refine ⟨1002876325541991743615623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1337168434055988991487497 1002876325541991743615623)
      ·
        refine ⟨1504314488312987615423435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002876325541991743615623 1504314488312987615423435)
        ·
          refine ⟨2256471732469481423135153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504314488312987615423435 2256471732469481423135153)
          ·
            refine ⟨1692353799352111067351365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256471732469481423135153 1692353799352111067351365)
            ·
              refine ⟨317316337378520825128381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1692353799352111067351365 317316337378520825128381)
              ·
                refine ⟨118993626516945309423143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317316337378520825128381 118993626516945309423143)
                ·
                  rfl

theorem cell19_391060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 3].length) (baseStart_391060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391060 prefixEnd_391060 := by exact prefixLift 391060
  have htrace : WordTrace (prefixWord ++ tailWord_391060) baseStart_391060 baseEnd_391060 := by
    simpa [prefixWord, tailWord_391060, baseEnd_391060] using wordTrace_append hprefix tailTrace_391060
  have hstable : (prefixWord ++ tailWord_391060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391060).length < 2 ^ (prefixWord ++ tailWord_391060).sum := by decide
  have hdescent : baseEnd_391060 < baseStart_391060 := by decide
  rcases family_descends (prefixWord ++ tailWord_391060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391138 : List Nat := [3, 3, 3, 1, 9]
def baseStart_391138 : Nat := 118140960795 + 391138 * 2 ^ 59
def prefixEnd_391138 : Nat := 4983230072969 + 3 ^ 40 * 391138 * 2
def baseEnd_391138 : Nat := 4408050397550527395911

theorem tailTrace_391138 : CollatzResearch.WordTrace tailWord_391138 prefixEnd_391138 4408050397550527395911 := by
  unfold tailWord_391138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3566493714245325474301517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9510649904654201264804045 3566493714245325474301517)
  ·
    refine ⟨1337435142841997052863069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3566493714245325474301517 1337435142841997052863069)
    ·
      refine ⟨501538178565748894823651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1337435142841997052863069 501538178565748894823651)
      ·
        refine ⟨752307267848623342235477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501538178565748894823651 752307267848623342235477)
        ·
          refine ⟨4408050397550527395911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 752307267848623342235477 4408050397550527395911)
          ·
            rfl

theorem cell19_391138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 9].length) (baseStart_391138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391138 prefixEnd_391138 := by exact prefixLift 391138
  have htrace : WordTrace (prefixWord ++ tailWord_391138) baseStart_391138 baseEnd_391138 := by
    simpa [prefixWord, tailWord_391138, baseEnd_391138] using wordTrace_append hprefix tailTrace_391138
  have hstable : (prefixWord ++ tailWord_391138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391138).length < 2 ^ (prefixWord ++ tailWord_391138).sum := by decide
  have hdescent : baseEnd_391138 < baseStart_391138 := by decide
  rcases family_descends (prefixWord ++ tailWord_391138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391172 : List Nat := [2, 3, 2, 4, 1, 1, 3, 3]
def baseStart_391172 : Nat := 118140960795 + 391172 * 2 ^ 59
def prefixEnd_391172 : Nat := 4983230072969 + 3 ^ 40 * 391172 * 2
def baseEnd_391172 : Nat := 119027706418162234933949

theorem tailTrace_391172 : CollatzResearch.WordTrace tailWord_391172 prefixEnd_391172 119027706418162234933949 := by
  unfold tailWord_391172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133607469429062851971885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9511476625905417135962513 7133607469429062851971885)
  ·
    refine ⟨2675102801035898569489457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7133607469429062851971885 2675102801035898569489457)
    ·
      refine ⟨2006327100776923927117093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2675102801035898569489457 2006327100776923927117093)
      ·
        refine ⟨376186331395673236334455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2006327100776923927117093 376186331395673236334455)
        ·
          refine ⟨564279497093509854501683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376186331395673236334455 564279497093509854501683)
          ·
            refine ⟨846419245640264781752525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564279497093509854501683 846419245640264781752525)
            ·
              refine ⟨317407217115099293157197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846419245640264781752525 317407217115099293157197)
              ·
                refine ⟨119027706418162234933949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317407217115099293157197 119027706418162234933949)
                ·
                  rfl

theorem cell19_391172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 3].length) (baseStart_391172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391172 prefixEnd_391172 := by exact prefixLift 391172
  have htrace : WordTrace (prefixWord ++ tailWord_391172) baseStart_391172 baseEnd_391172 := by
    simpa [prefixWord, tailWord_391172, baseEnd_391172] using wordTrace_append hprefix tailTrace_391172
  have hstable : (prefixWord ++ tailWord_391172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391172).length < 2 ^ (prefixWord ++ tailWord_391172).sum := by decide
  have hdescent : baseEnd_391172 < baseStart_391172 := by decide
  rcases family_descends (prefixWord ++ tailWord_391172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391176 : List Nat := [2, 1, 3, 2, 1, 2, 5, 3]
def baseStart_391176 : Nat := 118140960795 + 391176 * 2 ^ 59
def prefixEnd_391176 : Nat := 4983230072969 + 3 ^ 40 * 391176 * 2
def baseEnd_391176 : Nat := 119028923557491410845049

theorem tailTrace_391176 : CollatzResearch.WordTrace tailWord_391176 prefixEnd_391176 119028923557491410845049 := by
  unfold tailWord_391176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133680415421817193544691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9511573887229089591392921 7133680415421817193544691)
  ·
    refine ⟨10700520623132725790317037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7133680415421817193544691 10700520623132725790317037)
    ·
      refine ⟨4012695233674772171368889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10700520623132725790317037 4012695233674772171368889)
      ·
        refine ⟨3009521425256079128526667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4012695233674772171368889 3009521425256079128526667)
        ·
          refine ⟨4514282137884118692790001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3009521425256079128526667 4514282137884118692790001)
          ·
            refine ⟨3385711603413089019592501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4514282137884118692790001 3385711603413089019592501)
            ·
              refine ⟨317410462819977095586797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3385711603413089019592501 317410462819977095586797)
              ·
                refine ⟨119028923557491410845049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317410462819977095586797 119028923557491410845049)
                ·
                  rfl

theorem cell19_391176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_391176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391176 prefixEnd_391176 := by exact prefixLift 391176
  have htrace : WordTrace (prefixWord ++ tailWord_391176) baseStart_391176 baseEnd_391176 := by
    simpa [prefixWord, tailWord_391176, baseEnd_391176] using wordTrace_append hprefix tailTrace_391176
  have hstable : (prefixWord ++ tailWord_391176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391176).length < 2 ^ (prefixWord ++ tailWord_391176).sum := by decide
  have hdescent : baseEnd_391176 < baseStart_391176 := by decide
  rcases family_descends (prefixWord ++ tailWord_391176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391233 : List Nat := [1, 2, 5, 1, 2, 2, 1, 5]
def baseStart_391233 : Nat := 118140960795 + 391233 * 2 ^ 59
def prefixEnd_391233 : Nat := 4983230072969 + 3 ^ 40 * 391233 * 2
def baseEnd_391233 : Nat := 119046267792932167578227

theorem tailTrace_391233 : CollatzResearch.WordTrace tailWord_391233 prefixEnd_391233 119046267792932167578227 := by
  unfold tailWord_391233
  simp only [CollatzResearch.WordTrace]
  refine ⟨14269439791637133121914353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9512959861091422081276235 14269439791637133121914353)
  ·
    refine ⟨10702079843727849841435765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14269439791637133121914353 10702079843727849841435765)
    ·
      refine ⟨1003319985349485922634603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10702079843727849841435765 1003319985349485922634603)
      ·
        refine ⟨1504979978024228883951905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003319985349485922634603 1504979978024228883951905)
        ·
          refine ⟨1128734983518171662963929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1504979978024228883951905 1128734983518171662963929)
          ·
            refine ⟨846551237638628747222947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128734983518171662963929 846551237638628747222947)
            ·
              refine ⟨1269826856457943120834421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846551237638628747222947 1269826856457943120834421)
              ·
                refine ⟨119046267792932167578227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1269826856457943120834421 119046267792932167578227)
                ·
                  rfl

theorem cell19_391233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 5].length) (baseStart_391233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391233 prefixEnd_391233 := by exact prefixLift 391233
  have htrace : WordTrace (prefixWord ++ tailWord_391233) baseStart_391233 baseEnd_391233 := by
    simpa [prefixWord, tailWord_391233, baseEnd_391233] using wordTrace_append hprefix tailTrace_391233
  have hstable : (prefixWord ++ tailWord_391233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391233).length < 2 ^ (prefixWord ++ tailWord_391233).sum := by decide
  have hdescent : baseEnd_391233 < baseStart_391233 := by decide
  rcases family_descends (prefixWord ++ tailWord_391233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391250 : List Nat := [3, 2, 2, 1, 5, 1, 5]
def baseStart_391250 : Nat := 118140960795 + 391250 * 2 ^ 59
def prefixEnd_391250 : Nat := 4983230072969 + 3 ^ 40 * 391250 * 2
def baseEnd_391250 : Nat := 39683813545027055066801

theorem tailTrace_391250 : CollatzResearch.WordTrace tailWord_391250 prefixEnd_391250 39683813545027055066801 := by
  unfold tailWord_391250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567514958143886256320801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9513373221717030016855469 3567514958143886256320801)
  ·
    refine ⟨2675636218607914692240601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3567514958143886256320801 2675636218607914692240601)
    ·
      refine ⟨2006727163955936019180451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2675636218607914692240601 2006727163955936019180451)
      ·
        refine ⟨3010090745933904028770677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006727163955936019180451 3010090745933904028770677)
        ·
          refine ⟨282196007431303502697251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3010090745933904028770677 282196007431303502697251)
          ·
            refine ⟨423294011146955254045877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282196007431303502697251 423294011146955254045877)
            ·
              refine ⟨39683813545027055066801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 423294011146955254045877 39683813545027055066801)
              ·
                rfl

theorem cell19_391250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 5].length) (baseStart_391250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391250 prefixEnd_391250 := by exact prefixLift 391250
  have htrace : WordTrace (prefixWord ++ tailWord_391250) baseStart_391250 baseEnd_391250 := by
    simpa [prefixWord, tailWord_391250, baseEnd_391250] using wordTrace_append hprefix tailTrace_391250
  have hstable : (prefixWord ++ tailWord_391250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391250).length < 2 ^ (prefixWord ++ tailWord_391250).sum := by decide
  have hdescent : baseEnd_391250 < baseStart_391250 := by decide
  rcases family_descends (prefixWord ++ tailWord_391250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391273 : List Nat := [1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_391273 : Nat := 118140960795 + 391273 * 2 ^ 59
def prefixEnd_391273 : Nat := 4983230072969 + 3 ^ 40 * 391273 * 2
def baseEnd_391273 : Nat := 119058439186223926689229

theorem tailTrace_391273 : CollatzResearch.WordTrace tailWord_391273 prefixEnd_391273 119058439186223926689229 := by
  unfold tailWord_391273
  simp only [CollatzResearch.WordTrace]
  refine ⟨14270898711492219953370473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9513932474328146635580315 14270898711492219953370473)
  ·
    refine ⟨10703174033619164965027855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14270898711492219953370473 10703174033619164965027855)
    ·
      refine ⟨16054761050428747447541783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10703174033619164965027855 16054761050428747447541783)
      ·
        refine ⟨24082141575643121171312675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16054761050428747447541783 24082141575643121171312675)
        ·
          refine ⟨36123212363464681756969013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24082141575643121171312675 36123212363464681756969013)
          ·
            refine ⟨3386551159074813914715845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36123212363464681756969013 3386551159074813914715845)
            ·
              refine ⟨634978342326527609009221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3386551159074813914715845 634978342326527609009221)
              ·
                refine ⟨119058439186223926689229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 634978342326527609009221 119058439186223926689229)
                ·
                  rfl

theorem cell19_391273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_391273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391273 prefixEnd_391273 := by exact prefixLift 391273
  have htrace : WordTrace (prefixWord ++ tailWord_391273) baseStart_391273 baseEnd_391273 := by
    simpa [prefixWord, tailWord_391273, baseEnd_391273] using wordTrace_append hprefix tailTrace_391273
  have hstable : (prefixWord ++ tailWord_391273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391273).length < 2 ^ (prefixWord ++ tailWord_391273).sum := by decide
  have hdescent : baseEnd_391273 < baseStart_391273 := by decide
  rcases family_descends (prefixWord ++ tailWord_391273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391292 : List Nat := [2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_391292 : Nat := 118140960795 + 391292 * 2 ^ 59
def prefixEnd_391292 : Nat := 4983230072969 + 3 ^ 40 * 391292 * 2
def baseEnd_391292 : Nat := 119064220598037512266955

theorem tailTrace_391292 : CollatzResearch.WordTrace tailWord_391292 prefixEnd_391292 119064220598037512266955 := by
  unfold tailWord_391292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135795849211693099156065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9514394465615590798874753 7135795849211693099156065)
  ·
    refine ⟨5351846886908769824367049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7135795849211693099156065 5351846886908769824367049)
    ·
      refine ⟨4013885165181577368275287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5351846886908769824367049 4013885165181577368275287)
      ·
        refine ⟨6020827747772366052412931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4013885165181577368275287 6020827747772366052412931)
        ·
          refine ⟨9031241621658549078619397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6020827747772366052412931 9031241621658549078619397)
          ·
            refine ⟨1693357804060977952241137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9031241621658549078619397 1693357804060977952241137)
            ·
              refine ⟨1270018353045733464180853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693357804060977952241137 1270018353045733464180853)
              ·
                refine ⟨119064220598037512266955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1270018353045733464180853 119064220598037512266955)
                ·
                  rfl

theorem cell19_391292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_391292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391292 prefixEnd_391292 := by exact prefixLift 391292
  have htrace : WordTrace (prefixWord ++ tailWord_391292) baseStart_391292 baseEnd_391292 := by
    simpa [prefixWord, tailWord_391292, baseEnd_391292] using wordTrace_append hprefix tailTrace_391292
  have hstable : (prefixWord ++ tailWord_391292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391292).length < 2 ^ (prefixWord ++ tailWord_391292).sum := by decide
  have hdescent : baseEnd_391292 < baseStart_391292 := by decide
  rcases family_descends (prefixWord ++ tailWord_391292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391318 : List Nat := [5, 3, 2, 1, 2, 1, 1, 4]
def baseStart_391318 : Nat := 118140960795 + 391318 * 2 ^ 59
def prefixEnd_391318 : Nat := 4983230072969 + 3 ^ 40 * 391318 * 2
def baseEnd_391318 : Nat := 119072132003677155689107

theorem tailTrace_391318 : CollatzResearch.WordTrace tailWord_391318 prefixEnd_391318 119072132003677155689107 := by
  unfold tailWord_391318
  simp only [CollatzResearch.WordTrace]
  refine ⟨892033749770574539922413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9515026664219461759172405 892033749770574539922413)
  ·
    refine ⟨334512656163965452470905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 892033749770574539922413 334512656163965452470905)
    ·
      refine ⟨250884492122974089353179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334512656163965452470905 250884492122974089353179)
      ·
        refine ⟨376326738184461134029769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250884492122974089353179 376326738184461134029769)
        ·
          refine ⟨282245053638345850522327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 376326738184461134029769 282245053638345850522327)
          ·
            refine ⟨423367580457518775783491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282245053638345850522327 423367580457518775783491)
            ·
              refine ⟨635051370686278163675237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423367580457518775783491 635051370686278163675237)
              ·
                refine ⟨119072132003677155689107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635051370686278163675237 119072132003677155689107)
                ·
                  rfl

theorem cell19_391318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_391318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391318 prefixEnd_391318 := by exact prefixLift 391318
  have htrace : WordTrace (prefixWord ++ tailWord_391318) baseStart_391318 baseEnd_391318 := by
    simpa [prefixWord, tailWord_391318, baseEnd_391318] using wordTrace_append hprefix tailTrace_391318
  have hstable : (prefixWord ++ tailWord_391318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391318).length < 2 ^ (prefixWord ++ tailWord_391318).sum := by decide
  have hdescent : baseEnd_391318 < baseStart_391318 := by decide
  rcases family_descends (prefixWord ++ tailWord_391318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391328 : List Nat := [2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_391328 : Nat := 118140960795 + 391328 * 2 ^ 59
def prefixEnd_391328 : Nat := 4983230072969 + 3 ^ 40 * 391328 * 2
def baseEnd_391328 : Nat := 119075174852000095466857

theorem tailTrace_391328 : CollatzResearch.WordTrace tailWord_391328 prefixEnd_391328 119075174852000095466857 := by
  unfold tailWord_391328
  simp only [CollatzResearch.WordTrace]
  refine ⟨7136452363146482173311319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9515269817528642897748425 7136452363146482173311319)
  ·
    refine ⟨10704678544719723259966979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7136452363146482173311319 10704678544719723259966979)
    ·
      refine ⟨16057017817079584889950469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10704678544719723259966979 16057017817079584889950469)
      ·
        refine ⟨3010690840702422166865713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16057017817079584889950469 3010690840702422166865713)
        ·
          refine ⟨2258018130526816625149285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3010690840702422166865713 2258018130526816625149285)
          ·
            refine ⟨423378399473778117215491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2258018130526816625149285 423378399473778117215491)
            ·
              refine ⟨635067599210667175823237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423378399473778117215491 635067599210667175823237)
              ·
                refine ⟨119075174852000095466857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 635067599210667175823237 119075174852000095466857)
                ·
                  rfl

theorem cell19_391328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_391328 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391328 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391328 prefixEnd_391328 := by exact prefixLift 391328
  have htrace : WordTrace (prefixWord ++ tailWord_391328) baseStart_391328 baseEnd_391328 := by
    simpa [prefixWord, tailWord_391328, baseEnd_391328] using wordTrace_append hprefix tailTrace_391328
  have hstable : (prefixWord ++ tailWord_391328).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391328).length < 2 ^ (prefixWord ++ tailWord_391328).sum := by decide
  have hdescent : baseEnd_391328 < baseStart_391328 := by decide
  rcases family_descends (prefixWord ++ tailWord_391328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391345 : List Nat := [1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_391345 : Nat := 118140960795 + 391345 * 2 ^ 59
def prefixEnd_391345 : Nat := 4983230072969 + 3 ^ 40 * 391345 * 2
def baseEnd_391345 : Nat := 119080347694149093089033

theorem tailTrace_391345 : CollatzResearch.WordTrace tailWord_391345 prefixEnd_391345 119080347694149093089033 := by
  unfold tailWord_391345
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273524767231376249991489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9515683178154250833327659 14273524767231376249991489)
  ·
    refine ⟨10705143575423532187493617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14273524767231376249991489 10705143575423532187493617)
    ·
      refine ⟨8028857681567649140620213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10705143575423532187493617 8028857681567649140620213)
      ·
        refine ⟨752705407646967106933145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8028857681567649140620213 752705407646967106933145)
        ·
          refine ⟨564529055735225330199859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752705407646967106933145 564529055735225330199859)
          ·
            refine ⟨846793583602837995299789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564529055735225330199859 846793583602837995299789)
            ·
              refine ⟨317547593851064248237421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846793583602837995299789 317547593851064248237421)
              ·
                refine ⟨119080347694149093089033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317547593851064248237421 119080347694149093089033)
                ·
                  rfl

theorem cell19_391345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_391345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391345 prefixEnd_391345 := by exact prefixLift 391345
  have htrace : WordTrace (prefixWord ++ tailWord_391345) baseStart_391345 baseEnd_391345 := by
    simpa [prefixWord, tailWord_391345, baseEnd_391345] using wordTrace_append hprefix tailTrace_391345
  have hstable : (prefixWord ++ tailWord_391345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391345).length < 2 ^ (prefixWord ++ tailWord_391345).sum := by decide
  have hdescent : baseEnd_391345 < baseStart_391345 := by decide
  rcases family_descends (prefixWord ++ tailWord_391345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391503 : List Nat := [1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_391503 : Nat := 118140960795 + 391503 * 2 ^ 59
def prefixEnd_391503 : Nat := 4983230072969 + 3 ^ 40 * 391503 * 2
def baseEnd_391503 : Nat := 119128424697651541577491

theorem tailTrace_391503 : CollatzResearch.WordTrace tailWord_391503 prefixEnd_391503 119128424697651541577491 := by
  unfold tailWord_391503
  simp only [CollatzResearch.WordTrace]
  refine ⟨14279287500658969234243163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9519525000439312822828775 14279287500658969234243163)
  ·
    refine ⟨21418931250988453851364745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14279287500658969234243163 21418931250988453851364745)
    ·
      refine ⟨16064198438241340388523559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21418931250988453851364745 16064198438241340388523559)
      ·
        refine ⟨24096297657362010582785339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16064198438241340388523559 24096297657362010582785339)
        ·
          refine ⟨36144446486043015874178009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24096297657362010582785339 36144446486043015874178009)
          ·
            refine ⟨27108334864532261905633507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36144446486043015874178009 27108334864532261905633507)
            ·
              refine ⟨40662502296798392858450261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27108334864532261905633507 40662502296798392858450261)
              ·
                refine ⟨119128424697651541577491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40662502296798392858450261 119128424697651541577491)
                ·
                  rfl

theorem cell19_391503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_391503 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391503 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391503 prefixEnd_391503 := by exact prefixLift 391503
  have htrace : WordTrace (prefixWord ++ tailWord_391503) baseStart_391503 baseEnd_391503 := by
    simpa [prefixWord, tailWord_391503, baseEnd_391503] using wordTrace_append hprefix tailTrace_391503
  have hstable : (prefixWord ++ tailWord_391503).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391503).length < 2 ^ (prefixWord ++ tailWord_391503).sum := by decide
  have hdescent : baseEnd_391503 < baseStart_391503 := by decide
  rcases family_descends (prefixWord ++ tailWord_391503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391653 : List Nat := [1, 3, 1, 5, 2, 7]
def baseStart_391653 : Nat := 118140960795 + 391653 * 2 ^ 59
def prefixEnd_391653 : Nat := 4983230072969 + 3 ^ 40 * 391653 * 2
def baseEnd_391653 : Nat := 13241563046943959804861

theorem tailTrace_391653 : CollatzResearch.WordTrace tailWord_391653 prefixEnd_391653 13241563046943959804861 := by
  unfold tailWord_391653
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284758450115544852203613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9523172300077029901469075 14284758450115544852203613)
  ·
    refine ⟨5356784418793329319576355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14284758450115544852203613 5356784418793329319576355)
    ·
      refine ⟨8035176628189993979364533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5356784418793329319576355 8035176628189993979364533)
      ·
        refine ⟨753297808892811935565425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8035176628189993979364533 753297808892811935565425)
        ·
          refine ⟨564973356669608951674069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 753297808892811935565425 564973356669608951674069)
          ·
            refine ⟨13241563046943959804861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 564973356669608951674069 13241563046943959804861)
            ·
              rfl

theorem cell19_391653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 7].length) (baseStart_391653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391653 prefixEnd_391653 := by exact prefixLift 391653
  have htrace : WordTrace (prefixWord ++ tailWord_391653) baseStart_391653 baseEnd_391653 := by
    simpa [prefixWord, tailWord_391653, baseEnd_391653] using wordTrace_append hprefix tailTrace_391653
  have hstable : (prefixWord ++ tailWord_391653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391653).length < 2 ^ (prefixWord ++ tailWord_391653).sum := by decide
  have hdescent : baseEnd_391653 < baseStart_391653 := by decide
  rcases family_descends (prefixWord ++ tailWord_391653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391674 : List Nat := [3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_391674 : Nat := 118140960795 + 391674 * 2 ^ 59
def prefixEnd_391674 : Nat := 4983230072969 + 3 ^ 40 * 391674 * 2
def baseEnd_391674 : Nat := 119180457403973811777025

theorem tailTrace_391674 : CollatzResearch.WordTrace tailWord_391674 prefixEnd_391674 119180457403973811777025 := by
  unfold tailWord_391674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571381095759866359679519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9523682922026310292478717 3571381095759866359679519)
  ·
    refine ⟨5357071643639799539519279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3571381095759866359679519 5357071643639799539519279)
    ·
      refine ⟨8035607465459699309278919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5357071643639799539519279 8035607465459699309278919)
      ·
        refine ⟨12053411198189548963918379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8035607465459699309278919 12053411198189548963918379)
        ·
          refine ⟨18080116797284323445877569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12053411198189548963918379 18080116797284323445877569)
          ·
            refine ⟨13560087597963242584408177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18080116797284323445877569 13560087597963242584408177)
            ·
              refine ⟨10170065698472431938306133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13560087597963242584408177 10170065698472431938306133)
              ·
                refine ⟨119180457403973811777025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10170065698472431938306133 119180457403973811777025)
                ·
                  rfl

theorem cell19_391674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_391674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391674 prefixEnd_391674 := by exact prefixLift 391674
  have htrace : WordTrace (prefixWord ++ tailWord_391674) baseStart_391674 baseEnd_391674 := by
    simpa [prefixWord, tailWord_391674, baseEnd_391674] using wordTrace_append hprefix tailTrace_391674
  have hstable : (prefixWord ++ tailWord_391674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391674).length < 2 ^ (prefixWord ++ tailWord_391674).sum := by decide
  have hdescent : baseEnd_391674 < baseStart_391674 := by decide
  rcases family_descends (prefixWord ++ tailWord_391674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391731 : List Nat := [1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_391731 : Nat := 118140960795 + 391731 * 2 ^ 59
def prefixEnd_391731 : Nat := 4983230072969 + 3 ^ 40 * 391731 * 2
def baseEnd_391731 : Nat := 119197801639414568510203

theorem tailTrace_391731 : CollatzResearch.WordTrace tailWord_391731 prefixEnd_391731 119197801639414568510203 := by
  unfold tailWord_391731
  simp only [CollatzResearch.WordTrace]
  refine ⟨14287603343832964173543047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9525068895888642782362031 14287603343832964173543047)
  ·
    refine ⟨21431405015749446260314571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14287603343832964173543047 21431405015749446260314571)
    ·
      refine ⟨32147107523624169390471857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21431405015749446260314571 32147107523624169390471857)
      ·
        refine ⟨24110330642718127042853893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32147107523624169390471857 24110330642718127042853893)
        ·
          refine ⟨4520686995509648820535105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24110330642718127042853893 4520686995509648820535105)
          ·
            refine ⟨3390515246632236615401329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520686995509648820535105 3390515246632236615401329)
            ·
              refine ⟨2542886434974177461550997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390515246632236615401329 2542886434974177461550997)
              ·
                refine ⟨119197801639414568510203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2542886434974177461550997 119197801639414568510203)
                ·
                  rfl

theorem cell19_391731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_391731 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391731 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391731 prefixEnd_391731 := by exact prefixLift 391731
  have htrace : WordTrace (prefixWord ++ tailWord_391731) baseStart_391731 baseEnd_391731 := by
    simpa [prefixWord, tailWord_391731, baseEnd_391731] using wordTrace_append hprefix tailTrace_391731
  have hstable : (prefixWord ++ tailWord_391731).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391731).length < 2 ^ (prefixWord ++ tailWord_391731).sum := by decide
  have hdescent : baseEnd_391731 < baseStart_391731 := by decide
  rcases family_descends (prefixWord ++ tailWord_391731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391742 : List Nat := [4, 2, 1, 4, 1, 2, 2, 3]
def baseStart_391742 : Nat := 118140960795 + 391742 * 2 ^ 59
def prefixEnd_391742 : Nat := 4983230072969 + 3 ^ 40 * 391742 * 2
def baseEnd_391742 : Nat := 119201148772569802265729

theorem tailTrace_391742 : CollatzResearch.WordTrace tailWord_391742 prefixEnd_391742 119201148772569802265729 := by
  unfold tailWord_391742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786000568349139131524185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9525336364528742034795653 1786000568349139131524185)
  ·
    refine ⟨1339500426261854348643139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1786000568349139131524185 1339500426261854348643139)
    ·
      refine ⟨2009250639392781522964709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1339500426261854348643139 2009250639392781522964709)
      ·
        refine ⟨376734494886146535555883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2009250639392781522964709 376734494886146535555883)
        ·
          refine ⟨565101742329219803333825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376734494886146535555883 565101742329219803333825)
          ·
            refine ⟨423826306746914852500369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565101742329219803333825 423826306746914852500369)
            ·
              refine ⟨317869730060186139375277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423826306746914852500369 317869730060186139375277)
              ·
                refine ⟨119201148772569802265729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317869730060186139375277 119201148772569802265729)
                ·
                  rfl

theorem cell19_391742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_391742 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_391742 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_391742 prefixEnd_391742 := by exact prefixLift 391742
  have htrace : WordTrace (prefixWord ++ tailWord_391742) baseStart_391742 baseEnd_391742 := by
    simpa [prefixWord, tailWord_391742, baseEnd_391742] using wordTrace_append hprefix tailTrace_391742
  have hstable : (prefixWord ++ tailWord_391742).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391742).length < 2 ^ (prefixWord ++ tailWord_391742).sum := by decide
  have hdescent : baseEnd_391742 < baseStart_391742 := by decide
  rcases family_descends (prefixWord ++ tailWord_391742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
