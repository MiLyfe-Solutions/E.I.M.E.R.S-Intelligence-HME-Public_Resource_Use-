import V185TrunkScan23Chunk0319

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1891796 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_1891796 : Nat := 118140960795 + 1891796 * 2 ^ 59
def prefixEnd_1891796 : Nat := 4983230072969 + 3 ^ 40 * 1891796 * 2
def baseEnd_1891796 : Nat := 971400648253185573149795

theorem tailTrace_1891796 : CollatzResearch.WordTrace tailWord_1891796 prefixEnd_1891796 971400648253185573149795 := by
  unfold tailWord_1891796
  simp only [CollatzResearch.WordTrace]
  refine ⟨34499734327176829939579621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45999645769569106586106161 34499734327176829939579621)
  ·
    refine ⟨6468700186345655613671179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34499734327176829939579621 6468700186345655613671179)
    ·
      refine ⟨9703050279518483420506769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6468700186345655613671179 9703050279518483420506769)
      ·
        refine ⟨7277287709638862565380077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9703050279518483420506769 7277287709638862565380077)
        ·
          refine ⟨2728982891114573462017529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7277287709638862565380077 2728982891114573462017529)
          ·
            refine ⟨2046737168335930096513147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2728982891114573462017529 2046737168335930096513147)
            ·
              refine ⟨3070105752503895144769721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2046737168335930096513147 3070105752503895144769721)
              ·
                refine ⟨2302579314377921358577291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070105752503895144769721 2302579314377921358577291)
                ·
                  refine ⟨3453868971566882037865937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302579314377921358577291 3453868971566882037865937)
                  ·
                    refine ⟨2590401728675161528399453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3453868971566882037865937 2590401728675161528399453)
                    ·
                      refine ⟨971400648253185573149795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590401728675161528399453 971400648253185573149795)
                      ·
                        rfl

theorem cell23_1891796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_1891796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891796 prefixEnd_1891796 := by exact prefixLift 1891796
  have htrace : WordTrace (prefixWord ++ tailWord_1891796) baseStart_1891796 baseEnd_1891796 := by
    simpa [prefixWord, tailWord_1891796, baseEnd_1891796] using wordTrace_append hprefix tailTrace_1891796
  have hstable : (prefixWord ++ tailWord_1891796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891796).length < 2 ^ (prefixWord ++ tailWord_1891796).sum := by decide
  have hdescent : baseEnd_1891796 < baseStart_1891796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891808 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 8]
def baseStart_1891808 : Nat := 118140960795 + 1891808 * 2 ^ 59
def prefixEnd_1891808 : Nat := 4983230072969 + 3 ^ 40 * 1891808 * 2
def baseEnd_1891808 : Nat := 323802270007013175399913

theorem tailTrace_1891808 : CollatzResearch.WordTrace tailWord_1891808 prefixEnd_1891808 323802270007013175399913 := by
  unfold tailWord_1891808
  simp only [CollatzResearch.WordTrace]
  refine ⟨34499953165155092964298039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45999937553540123952397385 34499953165155092964298039)
  ·
    refine ⟨51749929747732639446447059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34499953165155092964298039 51749929747732639446447059)
    ·
      refine ⟨77624894621598959169670589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51749929747732639446447059 77624894621598959169670589)
      ·
        refine ⟨29109335483099609688626471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77624894621598959169670589 29109335483099609688626471)
        ·
          refine ⟨43664003224649414532939707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29109335483099609688626471 43664003224649414532939707)
          ·
            refine ⟨65496004836974121799409561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43664003224649414532939707 65496004836974121799409561)
            ·
              refine ⟨49122003627730591349557171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65496004836974121799409561 49122003627730591349557171)
              ·
                refine ⟨73683005441595887024335757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49122003627730591349557171 73683005441595887024335757)
                ·
                  refine ⟨27631127040598457634125909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73683005441595887024335757 27631127040598457634125909)
                  ·
                    refine ⟨323802270007013175399913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27631127040598457634125909 323802270007013175399913)
                    ·
                      rfl

theorem cell23_1891808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 8].length) (baseStart_1891808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891808 prefixEnd_1891808 := by exact prefixLift 1891808
  have htrace : WordTrace (prefixWord ++ tailWord_1891808) baseStart_1891808 baseEnd_1891808 := by
    simpa [prefixWord, tailWord_1891808, baseEnd_1891808] using wordTrace_append hprefix tailTrace_1891808
  have hstable : (prefixWord ++ tailWord_1891808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891808).length < 2 ^ (prefixWord ++ tailWord_1891808).sum := by decide
  have hdescent : baseEnd_1891808 < baseStart_1891808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891826 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1891826 : Nat := 118140960795 + 1891826 * 2 ^ 59
def prefixEnd_1891826 : Nat := 4983230072969 + 3 ^ 40 * 1891826 * 2
def baseEnd_1891826 : Nat := 971416052672820455774657

theorem tailTrace_1891826 : CollatzResearch.WordTrace tailWord_1891826 prefixEnd_1891826 971416052672820455774657 := by
  unfold tailWord_1891826
  simp only [CollatzResearch.WordTrace]
  refine ⟨17250140711061243750687833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46000375229496650001834221 17250140711061243750687833)
  ·
    refine ⟨12937605533295932813015875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17250140711061243750687833 12937605533295932813015875)
    ·
      refine ⟨19406408299943899219523813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12937605533295932813015875 19406408299943899219523813)
      ·
        refine ⟨3638701556239481103660715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19406408299943899219523813 3638701556239481103660715)
        ·
          refine ⟨5458052334359221655491073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638701556239481103660715 5458052334359221655491073)
          ·
            refine ⟨4093539250769416241618305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458052334359221655491073 4093539250769416241618305)
            ·
              refine ⟨3070154438077062181213729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4093539250769416241618305 3070154438077062181213729)
              ·
                refine ⟨2302615828557796635910297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3070154438077062181213729 2302615828557796635910297)
                ·
                  refine ⟨1726961871418347476932723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302615828557796635910297 1726961871418347476932723)
                  ·
                    refine ⟨2590442807127521215399085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1726961871418347476932723 2590442807127521215399085)
                    ·
                      refine ⟨971416052672820455774657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590442807127521215399085 971416052672820455774657)
                      ·
                        rfl

theorem cell23_1891826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1891826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891826 prefixEnd_1891826 := by exact prefixLift 1891826
  have htrace : WordTrace (prefixWord ++ tailWord_1891826) baseStart_1891826 baseEnd_1891826 := by
    simpa [prefixWord, tailWord_1891826, baseEnd_1891826] using wordTrace_append hprefix tailTrace_1891826
  have hstable : (prefixWord ++ tailWord_1891826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891826).length < 2 ^ (prefixWord ++ tailWord_1891826).sum := by decide
  have hdescent : baseEnd_1891826 < baseStart_1891826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891842 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1891842 : Nat := 118140960795 + 1891842 * 2 ^ 59
def prefixEnd_1891842 : Nat := 4983230072969 + 3 ^ 40 * 1891842 * 2
def baseEnd_1891842 : Nat := 323808089454430797724861

theorem tailTrace_1891842 : CollatzResearch.WordTrace tailWord_1891842 prefixEnd_1891842 323808089454430797724861 := by
  unfold tailWord_1891842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17250286603046752433833445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46000764274791339823555853 17250286603046752433833445)
  ·
    refine ⟨3234428738071266081343771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17250286603046752433833445 3234428738071266081343771)
    ·
      refine ⟨4851643107106899122015657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3234428738071266081343771 4851643107106899122015657)
      ·
        refine ⟨3638732330330174341511743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4851643107106899122015657 3638732330330174341511743)
        ·
          refine ⟨5458098495495261512267615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3638732330330174341511743 5458098495495261512267615)
          ·
            refine ⟨8187147743242892268401423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5458098495495261512267615 8187147743242892268401423)
            ·
              refine ⟨12280721614864338402602135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8187147743242892268401423 12280721614864338402602135)
              ·
                refine ⟨18421082422296507603903203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12280721614864338402602135 18421082422296507603903203)
                ·
                  refine ⟨27631623633444761405854805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18421082422296507603903203 27631623633444761405854805)
                  ·
                    refine ⟨323808089454430797724861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27631623633444761405854805 323808089454430797724861)
                    ·
                      rfl

theorem cell23_1891842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1891842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891842 prefixEnd_1891842 := by exact prefixLift 1891842
  have htrace : WordTrace (prefixWord ++ tailWord_1891842) baseStart_1891842 baseEnd_1891842 := by
    simpa [prefixWord, tailWord_1891842, baseEnd_1891842] using wordTrace_append hprefix tailTrace_1891842
  have hstable : (prefixWord ++ tailWord_1891842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891842).length < 2 ^ (prefixWord ++ tailWord_1891842).sum := by decide
  have hdescent : baseEnd_1891842 < baseStart_1891842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891849 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 2, 2, 2]
def baseStart_1891849 : Nat := 118140960795 + 1891849 * 2 ^ 59
def prefixEnd_1891849 : Nat := 4983230072969 + 3 ^ 40 * 1891849 * 2
def baseEnd_1891849 : Nat := 971427862727873865787051

theorem tailTrace_1891849 : CollatzResearch.WordTrace tailWord_1891849 prefixEnd_1891849 971427862727873865787051 := by
  unfold tailWord_1891849
  simp only [CollatzResearch.WordTrace]
  refine ⟨69001401723161649930838601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46000934482107766620559067 69001401723161649930838601)
  ·
    refine ⟨51751051292371237448128951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69001401723161649930838601 51751051292371237448128951)
    ·
      refine ⟨77626576938556856172193427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51751051292371237448128951 77626576938556856172193427)
      ·
        refine ⟨116439865407835284258290141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77626576938556856172193427 116439865407835284258290141)
        ·
          refine ⟨43664949527938231596858803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116439865407835284258290141 43664949527938231596858803)
          ·
            refine ⟨65497424291907347395288205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43664949527938231596858803 65497424291907347395288205)
            ·
              refine ⟨24561534109465255273233077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65497424291907347395288205 24561534109465255273233077)
              ·
                refine ⟨2302643822762367681865601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24561534109465255273233077 2302643822762367681865601)
                ·
                  refine ⟨1726982867071775761399201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2302643822762367681865601 1726982867071775761399201)
                  ·
                    refine ⟨1295237150303831821049401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1726982867071775761399201 1295237150303831821049401)
                    ·
                      refine ⟨971427862727873865787051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295237150303831821049401 971427862727873865787051)
                      ·
                        rfl

theorem cell23_1891849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 2, 2].length) (baseStart_1891849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891849 prefixEnd_1891849 := by exact prefixLift 1891849
  have htrace : WordTrace (prefixWord ++ tailWord_1891849) baseStart_1891849 baseEnd_1891849 := by
    simpa [prefixWord, tailWord_1891849, baseEnd_1891849] using wordTrace_append hprefix tailTrace_1891849
  have hstable : (prefixWord ++ tailWord_1891849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891849).length < 2 ^ (prefixWord ++ tailWord_1891849).sum := by decide
  have hdescent : baseEnd_1891849 < baseStart_1891849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891865 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 3]
def baseStart_1891865 : Nat := 118140960795 + 1891865 * 2 ^ 59
def prefixEnd_1891865 : Nat := 4983230072969 + 3 ^ 40 * 1891865 * 2
def baseEnd_1891865 : Nat := 971436078418345803186977

theorem tailTrace_1891865 : CollatzResearch.WordTrace tailWord_1891865 prefixEnd_1891865 971436078418345803186977 := by
  unfold tailWord_1891865
  simp only [CollatzResearch.WordTrace]
  refine ⟨69001985291103684663421049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46001323527402456442280699 69001985291103684663421049)
  ·
    refine ⟨51751488968327763497565787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69001985291103684663421049 51751488968327763497565787)
    ·
      refine ⟨77627233452491645246348681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51751488968327763497565787 77627233452491645246348681)
      ·
        refine ⟨58220425089368733934761511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77627233452491645246348681 58220425089368733934761511)
        ·
          refine ⟨87330637634053100902142267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58220425089368733934761511 87330637634053100902142267)
          ·
            refine ⟨130995956451079651353213401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87330637634053100902142267 130995956451079651353213401)
            ·
              refine ⟨98246967338309738514910051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130995956451079651353213401 98246967338309738514910051)
              ·
                refine ⟨147370451007464607772365077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98246967338309738514910051 147370451007464607772365077)
                ·
                  refine ⟨6907989890974903489329613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 147370451007464607772365077 6907989890974903489329613)
                  ·
                    refine ⟨2590496209115588808498605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6907989890974903489329613 2590496209115588808498605)
                    ·
                      refine ⟨971436078418345803186977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590496209115588808498605 971436078418345803186977)
                      ·
                        rfl

theorem cell23_1891865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_1891865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891865 prefixEnd_1891865 := by exact prefixLift 1891865
  have htrace : WordTrace (prefixWord ++ tailWord_1891865) baseStart_1891865 baseEnd_1891865 := by
    simpa [prefixWord, tailWord_1891865, baseEnd_1891865] using wordTrace_append hprefix tailTrace_1891865
  have hstable : (prefixWord ++ tailWord_1891865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891865).length < 2 ^ (prefixWord ++ tailWord_1891865).sum := by decide
  have hdescent : baseEnd_1891865 < baseStart_1891865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891882 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1891882 : Nat := 118140960795 + 1891882 * 2 ^ 59
def prefixEnd_1891882 : Nat := 4983230072969 + 3 ^ 40 * 1891882 * 2
def baseEnd_1891882 : Nat := 971444807589472236674399

theorem tailTrace_1891882 : CollatzResearch.WordTrace tailWord_1891882 prefixEnd_1891882 971444807589472236674399 := by
  unfold tailWord_1891882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17250651333010524141697475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46001736888028064377859933 17250651333010524141697475)
  ·
    refine ⟨25875976999515786212546213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17250651333010524141697475 25875976999515786212546213)
    ·
      refine ⟨4851745687409209914852415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25875976999515786212546213 4851745687409209914852415)
      ·
        refine ⟨7277618531113814872278623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4851745687409209914852415 7277618531113814872278623)
        ·
          refine ⟨10916427796670722308417935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7277618531113814872278623 10916427796670722308417935)
          ·
            refine ⟨16374641695006083462626903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10916427796670722308417935 16374641695006083462626903)
            ·
              refine ⟨24561962542509125193940355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16374641695006083462626903 24561962542509125193940355)
              ·
                refine ⟨36842943813763687790910533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24561962542509125193940355 36842943813763687790910533)
                ·
                  refine ⟨6908051965080691460795725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36842943813763687790910533 6908051965080691460795725)
                  ·
                    refine ⟨2590519486905259297798397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6908051965080691460795725 2590519486905259297798397)
                    ·
                      refine ⟨971444807589472236674399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590519486905259297798397 971444807589472236674399)
                      ·
                        rfl

theorem cell23_1891882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1891882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891882 prefixEnd_1891882 := by exact prefixLift 1891882
  have htrace : WordTrace (prefixWord ++ tailWord_1891882) baseStart_1891882 baseEnd_1891882 := by
    simpa [prefixWord, tailWord_1891882, baseEnd_1891882] using wordTrace_append hprefix tailTrace_1891882
  have hstable : (prefixWord ++ tailWord_1891882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891882).length < 2 ^ (prefixWord ++ tailWord_1891882).sum := by decide
  have hdescent : baseEnd_1891882 < baseStart_1891882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891922 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1891922 : Nat := 118140960795 + 1891922 * 2 ^ 59
def prefixEnd_1891922 : Nat := 4983230072969 + 3 ^ 40 * 1891922 * 2
def baseEnd_1891922 : Nat := 971465346815652080174215

theorem tailTrace_1891922 : CollatzResearch.WordTrace tailWord_1891922 prefixEnd_1891922 971465346815652080174215 := by
  unfold tailWord_1891922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17251016062974295849561505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46002709501264788932164013 17251016062974295849561505)
  ·
    refine ⟨12938262047230721887171129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17251016062974295849561505 12938262047230721887171129)
    ·
      refine ⟨9703696535423041415378347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12938262047230721887171129 9703696535423041415378347)
      ·
        refine ⟨14555544803134562123067521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9703696535423041415378347 14555544803134562123067521)
        ·
          refine ⟨10916658602350921592300641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14555544803134562123067521 10916658602350921592300641)
          ·
            refine ⟨8187493951763191194225481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10916658602350921592300641 8187493951763191194225481)
            ·
              refine ⟨6140620463822393395669111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8187493951763191194225481 6140620463822393395669111)
              ·
                refine ⟨9210930695733590093503667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140620463822393395669111 9210930695733590093503667)
                ·
                  refine ⟨13816396043600385140255501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9210930695733590093503667 13816396043600385140255501)
                  ·
                    refine ⟨5181148516350144427595813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13816396043600385140255501 5181148516350144427595813)
                    ·
                      refine ⟨971465346815652080174215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5181148516350144427595813 971465346815652080174215)
                      ·
                        rfl

theorem cell23_1891922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1891922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891922 prefixEnd_1891922 := by exact prefixLift 1891922
  have htrace : WordTrace (prefixWord ++ tailWord_1891922) baseStart_1891922 baseEnd_1891922 := by
    simpa [prefixWord, tailWord_1891922, baseEnd_1891922] using wordTrace_append hprefix tailTrace_1891922
  have hstable : (prefixWord ++ tailWord_1891922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891922).length < 2 ^ (prefixWord ++ tailWord_1891922).sum := by decide
  have hdescent : baseEnd_1891922 < baseStart_1891922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891925 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 5]
def baseStart_1891925 : Nat := 118140960795 + 1891925 * 2 ^ 59
def prefixEnd_1891925 : Nat := 4983230072969 + 3 ^ 40 * 1891925 * 2
def baseEnd_1891925 : Nat := 971466887257615568436701

theorem tailTrace_1891925 : CollatzResearch.WordTrace tailWord_1891925 prefixEnd_1891925 971466887257615568436701 := by
  unfold tailWord_1891925
  simp only [CollatzResearch.WordTrace]
  refine ⟨69004173670886314910605229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46002782447257543273736819 69004173670886314910605229)
  ·
    refine ⟨25876565126582368091476961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69004173670886314910605229 25876565126582368091476961)
    ·
      refine ⟨19407423844936776068607721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25876565126582368091476961 19407423844936776068607721)
      ·
        refine ⟨14555567883702582051455791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19407423844936776068607721 14555567883702582051455791)
        ·
          refine ⟨21833351825553873077183687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14555567883702582051455791 21833351825553873077183687)
          ·
            refine ⟨32750027738330809615775531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21833351825553873077183687 32750027738330809615775531)
            ·
              refine ⟨49125041607496214423663297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32750027738330809615775531 49125041607496214423663297)
              ·
                refine ⟨36843781205622160817747473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49125041607496214423663297 36843781205622160817747473)
                ·
                  refine ⟨27632835904216620613310605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36843781205622160817747473 27632835904216620613310605)
                  ·
                    refine ⟨10362313464081232729991477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27632835904216620613310605 10362313464081232729991477)
                    ·
                      refine ⟨971466887257615568436701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10362313464081232729991477 971466887257615568436701)
                      ·
                        rfl

theorem cell23_1891925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_1891925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891925 prefixEnd_1891925 := by exact prefixLift 1891925
  have htrace : WordTrace (prefixWord ++ tailWord_1891925) baseStart_1891925 baseEnd_1891925 := by
    simpa [prefixWord, tailWord_1891925, baseEnd_1891925] using wordTrace_append hprefix tailTrace_1891925
  have hstable : (prefixWord ++ tailWord_1891925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891925).length < 2 ^ (prefixWord ++ tailWord_1891925).sum := by decide
  have hdescent : baseEnd_1891925 < baseStart_1891925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891945 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 8]
def baseStart_1891945 : Nat := 118140960795 + 1891945 * 2 ^ 59
def prefixEnd_1891945 : Nat := 4983230072969 + 3 ^ 40 * 1891945 * 2
def baseEnd_1891945 : Nat := 107941906318967276687401

theorem tailTrace_1891945 : CollatzResearch.WordTrace tailWord_1891945 prefixEnd_1891945 107941906318967276687401 := by
  unfold tailWord_1891945
  simp only [CollatzResearch.WordTrace]
  refine ⟨69004903130813858326333289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46003268753875905550888859 69004903130813858326333289)
  ·
    refine ⟨51753677348110393744749967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69004903130813858326333289 51753677348110393744749967)
    ·
      refine ⟨77630516022165590617124951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51753677348110393744749967 77630516022165590617124951)
      ·
        refine ⟨116445774033248385925687427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77630516022165590617124951 116445774033248385925687427)
        ·
          refine ⟨174668661049872578888531141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116445774033248385925687427 174668661049872578888531141)
          ·
            refine ⟨32750373946851108541599589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174668661049872578888531141 32750373946851108541599589)
            ·
              refine ⟨6140695115034582851549923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32750373946851108541599589 6140695115034582851549923)
              ·
                refine ⟨9211042672551874277324885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6140695115034582851549923 9211042672551874277324885)
                ·
                  refine ⟨107941906318967276687401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9211042672551874277324885 107941906318967276687401)
                  ·
                    rfl

theorem cell23_1891945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 8].length) (baseStart_1891945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891945 prefixEnd_1891945 := by exact prefixLift 1891945
  have htrace : WordTrace (prefixWord ++ tailWord_1891945) baseStart_1891945 baseEnd_1891945 := by
    simpa [prefixWord, tailWord_1891945, baseEnd_1891945] using wordTrace_append hprefix tailTrace_1891945
  have hstable : (prefixWord ++ tailWord_1891945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891945).length < 2 ^ (prefixWord ++ tailWord_1891945).sum := by decide
  have hdescent : baseEnd_1891945 < baseStart_1891945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1891985 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_1891985 : Nat := 118140960795 + 1891985 * 2 ^ 59
def prefixEnd_1891985 : Nat := 4983230072969 + 3 ^ 40 * 1891985 * 2
def baseEnd_1891985 : Nat := 971497696096885333686425

theorem tailTrace_1891985 : CollatzResearch.WordTrace tailWord_1891985 prefixEnd_1891985 971497696096885333686425 := by
  unfold tailWord_1891985
  simp only [CollatzResearch.WordTrace]
  refine ⟨69006362050668945157789409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46004241367112630105192939 69006362050668945157789409)
  ·
    refine ⟨51754771538001708868342057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69006362050668945157789409 51754771538001708868342057)
    ·
      refine ⟨38816078653501281651256543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51754771538001708868342057 38816078653501281651256543)
      ·
        refine ⟨58224117980251922476884815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38816078653501281651256543 58224117980251922476884815)
        ·
          refine ⟨87336176970377883715327223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58224117980251922476884815 87336176970377883715327223)
          ·
            refine ⟨131004265455566825572990835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87336176970377883715327223 131004265455566825572990835)
            ·
              refine ⟨196506398183350238359486253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131004265455566825572990835 196506398183350238359486253)
              ·
                refine ⟨73689899318756339384807345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196506398183350238359486253 73689899318756339384807345)
                ·
                  refine ⟨55267424489067254538605509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73689899318756339384807345 55267424489067254538605509)
                  ·
                    refine ⟨10362642091700110225988533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55267424489067254538605509 10362642091700110225988533)
                    ·
                      refine ⟨971497696096885333686425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10362642091700110225988533 971497696096885333686425)
                      ·
                        rfl

theorem cell23_1891985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_1891985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1891985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1891985 prefixEnd_1891985 := by exact prefixLift 1891985
  have htrace : WordTrace (prefixWord ++ tailWord_1891985) baseStart_1891985 baseEnd_1891985 := by
    simpa [prefixWord, tailWord_1891985, baseEnd_1891985] using wordTrace_append hprefix tailTrace_1891985
  have hstable : (prefixWord ++ tailWord_1891985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1891985).length < 2 ^ (prefixWord ++ tailWord_1891985).sum := by decide
  have hdescent : baseEnd_1891985 < baseStart_1891985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1891985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892029 : List Nat := [1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1892029 : Nat := 118140960795 + 1892029 * 2 ^ 59
def prefixEnd_1892029 : Nat := 4983230072969 + 3 ^ 40 * 1892029 * 2
def baseEnd_1892029 : Nat := 971520289245683161536223

theorem tailTrace_1892029 : CollatzResearch.WordTrace tailWord_1892029 prefixEnd_1892029 971520289245683161536223 := by
  unfold tailWord_1892029
  simp only [CollatzResearch.WordTrace]
  refine ⟨69007966862509540672391141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46005311241673027114927427 69007966862509540672391141)
  ·
    refine ⟨12938993786720538876073339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69007966862509540672391141 12938993786720538876073339)
    ·
      refine ⟨19408490680080808314110009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12938993786720538876073339 19408490680080808314110009)
      ·
        refine ⟨14556368010060606235582507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19408490680080808314110009 14556368010060606235582507)
        ·
          refine ⟨21834552015090909353373761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14556368010060606235582507 21834552015090909353373761)
          ·
            refine ⟨16375914011318182015030321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21834552015090909353373761 16375914011318182015030321)
            ·
              refine ⟨12281935508488636511272741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16375914011318182015030321 12281935508488636511272741)
              ·
                refine ⟨2302862907841619345863639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12281935508488636511272741 2302862907841619345863639)
                ·
                  refine ⟨3454294361762429018795459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2302862907841619345863639 3454294361762429018795459)
                  ·
                    refine ⟨5181441542643643528193189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3454294361762429018795459 5181441542643643528193189)
                    ·
                      refine ⟨971520289245683161536223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5181441542643643528193189 971520289245683161536223)
                      ·
                        rfl

theorem cell23_1892029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1892029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892029 prefixEnd_1892029 := by exact prefixLift 1892029
  have htrace : WordTrace (prefixWord ++ tailWord_1892029) baseStart_1892029 baseEnd_1892029 := by
    simpa [prefixWord, tailWord_1892029, baseEnd_1892029] using wordTrace_append hprefix tailTrace_1892029
  have hstable : (prefixWord ++ tailWord_1892029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892029).length < 2 ^ (prefixWord ++ tailWord_1892029).sum := by decide
  have hdescent : baseEnd_1892029 < baseStart_1892029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892046 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_1892046 : Nat := 118140960795 + 1892046 * 2 ^ 59
def prefixEnd_1892046 : Nat := 4983230072969 + 3 ^ 40 * 1892046 * 2
def baseEnd_1892046 : Nat := 971529018416809595023645

theorem tailTrace_1892046 : CollatzResearch.WordTrace tailWord_1892046 prefixEnd_1892046 971529018416809595023645 := by
  unfold tailWord_1892046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626073362930994071969999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46005724602298635050506661 8626073362930994071969999)
  ·
    refine ⟨12939110044396491107954999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8626073362930994071969999 12939110044396491107954999)
    ·
      refine ⟨19408665066594736661932499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12939110044396491107954999 19408665066594736661932499)
      ·
        refine ⟨29112997599892104992898749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19408665066594736661932499 29112997599892104992898749)
        ·
          refine ⟨10917374099959539372337031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29112997599892104992898749 10917374099959539372337031)
          ·
            refine ⟨16376061149939309058505547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917374099959539372337031 16376061149939309058505547)
            ·
              refine ⟨24564091724908963587758321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16376061149939309058505547 24564091724908963587758321)
              ·
                refine ⟨18423068793681722690818741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24564091724908963587758321 18423068793681722690818741)
                ·
                  refine ⟨1727162699407661502264257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18423068793681722690818741 1727162699407661502264257)
                  ·
                    refine ⟨1295372024555746126698193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727162699407661502264257 1295372024555746126698193)
                    ·
                      refine ⟨971529018416809595023645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295372024555746126698193 971529018416809595023645)
                      ·
                        rfl

theorem cell23_1892046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_1892046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892046 prefixEnd_1892046 := by exact prefixLift 1892046
  have htrace : WordTrace (prefixWord ++ tailWord_1892046) baseStart_1892046 baseEnd_1892046 := by
    simpa [prefixWord, tailWord_1892046, baseEnd_1892046] using wordTrace_append hprefix tailTrace_1892046
  have hstable : (prefixWord ++ tailWord_1892046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892046).length < 2 ^ (prefixWord ++ tailWord_1892046).sum := by decide
  have hdescent : baseEnd_1892046 < baseStart_1892046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892063 : List Nat := [1, 1, 2, 3, 2, 2, 1, 6, 1, 2, 2]
def baseStart_1892063 : Nat := 118140960795 + 1892063 * 2 ^ 59
def prefixEnd_1892063 : Nat := 4983230072969 + 3 ^ 40 * 1892063 * 2
def baseEnd_1892063 : Nat := 971537747587936028511067

theorem tailTrace_1892063 : CollatzResearch.WordTrace tailWord_1892063 prefixEnd_1892063 971537747587936028511067 := by
  unfold tailWord_1892063
  simp only [CollatzResearch.WordTrace]
  refine ⟨69009206944386364479128843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46006137962924242986085895 69009206944386364479128843)
  ·
    refine ⟨103513810416579546718693265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69009206944386364479128843 103513810416579546718693265)
    ·
      refine ⟨77635357812434660039019949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103513810416579546718693265 77635357812434660039019949)
      ·
        refine ⟨29113259179662997514632481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77635357812434660039019949 29113259179662997514632481)
        ·
          refine ⟨21834944384747248135974361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29113259179662997514632481 21834944384747248135974361)
          ·
            refine ⟨16376208288560436101980771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21834944384747248135974361 16376208288560436101980771)
            ·
              refine ⟨24564312432840654152971157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16376208288560436101980771 24564312432840654152971157)
              ·
                refine ⟨1151452145289405663420523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24564312432840654152971157 1151452145289405663420523)
                ·
                  refine ⟨1727178217934108495130785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151452145289405663420523 1727178217934108495130785)
                  ·
                    refine ⟨1295383663450581371348089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727178217934108495130785 1295383663450581371348089)
                    ·
                      refine ⟨971537747587936028511067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295383663450581371348089 971537747587936028511067)
                      ·
                        rfl

theorem cell23_1892063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_1892063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892063 prefixEnd_1892063 := by exact prefixLift 1892063
  have htrace : WordTrace (prefixWord ++ tailWord_1892063) baseStart_1892063 baseEnd_1892063 := by
    simpa [prefixWord, tailWord_1892063, baseEnd_1892063] using wordTrace_append hprefix tailTrace_1892063
  have hstable : (prefixWord ++ tailWord_1892063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892063).length < 2 ^ (prefixWord ++ tailWord_1892063).sum := by decide
  have hdescent : baseEnd_1892063 < baseStart_1892063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892086 : List Nat := [5, 1, 1, 1, 1, 5, 2, 7]
def baseStart_1892086 : Nat := 118140960795 + 1892086 * 2 ^ 59
def prefixEnd_1892086 : Nat := 4983230072969 + 3 ^ 40 * 1892086 * 2
def baseEnd_1892086 : Nat := 35983316949740349574943

theorem tailTrace_1892086 : CollatzResearch.WordTrace tailWord_1892086 prefixEnd_1892086 35983316949740349574943 := by
  unfold tailWord_1892086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313127863956439962951007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46006697215535359604810741 4313127863956439962951007)
  ·
    refine ⟨6469691795934659944426511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4313127863956439962951007 6469691795934659944426511)
    ·
      refine ⟨9704537693901989916639767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6469691795934659944426511 9704537693901989916639767)
      ·
        refine ⟨14556806540852984874959651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9704537693901989916639767 14556806540852984874959651)
        ·
          refine ⟨21835209811279477312439477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14556806540852984874959651 21835209811279477312439477)
          ·
            refine ⟨2047050919807450998041201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21835209811279477312439477 2047050919807450998041201)
            ·
              refine ⟨1535288189855588248530901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047050919807450998041201 1535288189855588248530901)
              ·
                refine ⟨35983316949740349574943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1535288189855588248530901 35983316949740349574943)
                ·
                  rfl

theorem cell23_1892086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_1892086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892086 prefixEnd_1892086 := by exact prefixLift 1892086
  have htrace : WordTrace (prefixWord ++ tailWord_1892086) baseStart_1892086 baseEnd_1892086 := by
    simpa [prefixWord, tailWord_1892086, baseEnd_1892086] using wordTrace_append hprefix tailTrace_1892086
  have hstable : (prefixWord ++ tailWord_1892086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892086).length < 2 ^ (prefixWord ++ tailWord_1892086).sum := by decide
  have hdescent : baseEnd_1892086 < baseStart_1892086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892092 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 4, 5]
def baseStart_1892092 : Nat := 118140960795 + 1892092 * 2 ^ 59
def prefixEnd_1892092 : Nat := 4983230072969 + 3 ^ 40 * 1892092 * 2
def baseEnd_1892092 : Nat := 971552638526916415048433

theorem tailTrace_1892092 : CollatzResearch.WordTrace tailWord_1892092 prefixEnd_1892092 971552638526916415048433 := by
  unfold tailWord_1892092
  simp only [CollatzResearch.WordTrace]
  refine ⟨34505132330640651215967265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46006843107520868287956353 34505132330640651215967265)
  ·
    refine ⟨25878849247980488411975449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34505132330640651215967265 25878849247980488411975449)
    ·
      refine ⟨19409136935985366308981587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25878849247980488411975449 19409136935985366308981587)
      ·
        refine ⟨29113705403978049463472381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19409136935985366308981587 29113705403978049463472381)
        ·
          refine ⟨10917639526491768548802143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29113705403978049463472381 10917639526491768548802143)
          ·
            refine ⟨16376459289737652823203215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10917639526491768548802143 16376459289737652823203215)
            ·
              refine ⟨24564688934606479234804823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16376459289737652823203215 24564688934606479234804823)
              ·
                refine ⟨36847033401909718852207235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24564688934606479234804823 36847033401909718852207235)
                ·
                  refine ⟨55270550102864578278310853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36847033401909718852207235 55270550102864578278310853)
                  ·
                    refine ⟨10363228144287108427183285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 55270550102864578278310853 10363228144287108427183285)
                    ·
                      refine ⟨971552638526916415048433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10363228144287108427183285 971552638526916415048433)
                      ·
                        rfl

theorem cell23_1892092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_1892092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892092 prefixEnd_1892092 := by exact prefixLift 1892092
  have htrace : WordTrace (prefixWord ++ tailWord_1892092) baseStart_1892092 baseEnd_1892092 := by
    simpa [prefixWord, tailWord_1892092, baseEnd_1892092] using wordTrace_append hprefix tailTrace_1892092
  have hstable : (prefixWord ++ tailWord_1892092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892092).length < 2 ^ (prefixWord ++ tailWord_1892092).sum := by decide
  have hdescent : baseEnd_1892092 < baseStart_1892092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892114 : List Nat := [3, 2, 4, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1892114 : Nat := 118140960795 + 1892114 * 2 ^ 59
def prefixEnd_1892114 : Nat := 4983230072969 + 3 ^ 40 * 1892114 * 2
def baseEnd_1892114 : Nat := 971563935101315328973333

theorem tailTrace_1892114 : CollatzResearch.WordTrace tailWord_1892114 prefixEnd_1892114 971563935101315328973333 := by
  unfold tailWord_1892114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17252766766800400047308849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46007378044801066792823597 17252766766800400047308849)
  ·
    refine ⟨12939575075100300035481637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17252766766800400047308849 12939575075100300035481637)
    ·
      refine ⟨2426170326581306256652807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12939575075100300035481637 2426170326581306256652807)
      ·
        refine ⟨3639255489871959384979211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2426170326581306256652807 3639255489871959384979211)
        ·
          refine ⟨5458883234807939077468817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639255489871959384979211 5458883234807939077468817)
          ·
            refine ⟨4094162426105954308101613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5458883234807939077468817 4094162426105954308101613)
            ·
              refine ⟨1535310909789732865538105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094162426105954308101613 1535310909789732865538105)
              ·
                refine ⟨1151483182342299649153579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535310909789732865538105 1151483182342299649153579)
                ·
                  refine ⟨1727224773513449473730369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151483182342299649153579 1727224773513449473730369)
                  ·
                    refine ⟨1295418580135087105297777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727224773513449473730369 1295418580135087105297777)
                    ·
                      refine ⟨971563935101315328973333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295418580135087105297777 971563935101315328973333)
                      ·
                        rfl

theorem cell23_1892114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1892114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892114 prefixEnd_1892114 := by exact prefixLift 1892114
  have htrace : WordTrace (prefixWord ++ tailWord_1892114) baseStart_1892114 baseEnd_1892114 := by
    simpa [prefixWord, tailWord_1892114, baseEnd_1892114] using wordTrace_append hprefix tailTrace_1892114
  have hstable : (prefixWord ++ tailWord_1892114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892114).length < 2 ^ (prefixWord ++ tailWord_1892114).sum := by decide
  have hdescent : baseEnd_1892114 < baseStart_1892114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892169 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 3]
def baseStart_1892169 : Nat := 118140960795 + 1892169 * 2 ^ 59
def prefixEnd_1892169 : Nat := 4983230072969 + 3 ^ 40 * 1892169 * 2
def baseEnd_1892169 : Nat := 971592176537312613785579

theorem tailTrace_1892169 : CollatzResearch.WordTrace tailWord_1892169 prefixEnd_1892169 971592176537312613785579 := by
  unfold tailWord_1892169
  simp only [CollatzResearch.WordTrace]
  refine ⟨69013073082002344582487561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46008715388001563054991707 69013073082002344582487561)
  ·
    refine ⟨51759804811501758436865671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69013073082002344582487561 51759804811501758436865671)
    ·
      refine ⟨77639707217252637655298507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51759804811501758436865671 77639707217252637655298507)
      ·
        refine ⟨116459560825878956482947761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77639707217252637655298507 116459560825878956482947761)
        ·
          refine ⟨87344670619409217362210821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116459560825878956482947761 87344670619409217362210821)
          ·
            refine ⟨16377125741139228255414529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87344670619409217362210821 16377125741139228255414529)
            ·
              refine ⟨12282844305854421191560897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16377125741139228255414529 12282844305854421191560897)
              ·
                refine ⟨9212133229390815893670673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12282844305854421191560897 9212133229390815893670673)
                ·
                  refine ⟨6909099922043111920253005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9212133229390815893670673 6909099922043111920253005)
                  ·
                    refine ⟨2590912470766166970094877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6909099922043111920253005 2590912470766166970094877)
                    ·
                      refine ⟨971592176537312613785579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2590912470766166970094877 971592176537312613785579)
                      ·
                        rfl

theorem cell23_1892169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_1892169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892169 prefixEnd_1892169 := by exact prefixLift 1892169
  have htrace : WordTrace (prefixWord ++ tailWord_1892169) baseStart_1892169 baseEnd_1892169 := by
    simpa [prefixWord, tailWord_1892169, baseEnd_1892169] using wordTrace_append hprefix tailTrace_1892169
  have hstable : (prefixWord ++ tailWord_1892169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892169).length < 2 ^ (prefixWord ++ tailWord_1892169).sum := by decide
  have hdescent : baseEnd_1892169 < baseStart_1892169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892206 : List Nat := [4, 1, 2, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1892206 : Nat := 118140960795 + 1892206 * 2 ^ 59
def prefixEnd_1892206 : Nat := 4983230072969 + 3 ^ 40 * 1892206 * 2
def baseEnd_1892206 : Nat := 323870391773842989674303

theorem tailTrace_1892206 : CollatzResearch.WordTrace tailWord_1892206 prefixEnd_1892206 323870391773842989674303 := by
  unfold tailWord_1892206
  simp only [CollatzResearch.WordTrace]
  refine ⟨8626802822858537487698059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46009615055245533267722981 8626802822858537487698059)
  ·
    refine ⟨12940204234287806231547089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8626802822858537487698059 12940204234287806231547089)
    ·
      refine ⟨9705153175715854673660317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12940204234287806231547089 9705153175715854673660317)
      ·
        refine ⟨3639432440893445502622619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9705153175715854673660317 3639432440893445502622619)
        ·
          refine ⟨5459148661340168253933929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3639432440893445502622619 5459148661340168253933929)
          ·
            refine ⟨4094361496005126190450447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5459148661340168253933929 4094361496005126190450447)
            ·
              refine ⟨6141542244007689285675671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4094361496005126190450447 6141542244007689285675671)
              ·
                refine ⟨9212313366011533928513507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141542244007689285675671 9212313366011533928513507)
                ·
                  refine ⟨13818470049017300892770261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9212313366011533928513507 13818470049017300892770261)
                  ·
                    refine ⟨323870391773842989674303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13818470049017300892770261 323870391773842989674303)
                    ·
                      rfl

theorem cell23_1892206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1892206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892206 prefixEnd_1892206 := by exact prefixLift 1892206
  have htrace : WordTrace (prefixWord ++ tailWord_1892206) baseStart_1892206 baseEnd_1892206 := by
    simpa [prefixWord, tailWord_1892206, baseEnd_1892206] using wordTrace_append hprefix tailTrace_1892206
  have hstable : (prefixWord ++ tailWord_1892206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892206).length < 2 ^ (prefixWord ++ tailWord_1892206).sum := by decide
  have hdescent : baseEnd_1892206 < baseStart_1892206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892209 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1892209 : Nat := 118140960795 + 1892209 * 2 ^ 59
def prefixEnd_1892209 : Nat := 4983230072969 + 3 ^ 40 * 1892209 * 2
def baseEnd_1892209 : Nat := 971612715763492457285395

theorem tailTrace_1892209 : CollatzResearch.WordTrace tailWord_1892209 prefixEnd_1892209 971612715763492457285395 := by
  unfold tailWord_1892209
  simp only [CollatzResearch.WordTrace]
  refine ⟨69014532001857431413943681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46009688001238287609295787 69014532001857431413943681)
  ·
    refine ⟨51760899001393073560457761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69014532001857431413943681 51760899001393073560457761)
    ·
      refine ⟨38820674251044805170343321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51760899001393073560457761 38820674251044805170343321)
      ·
        refine ⟨29115505688283603877757491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38820674251044805170343321 29115505688283603877757491)
        ·
          refine ⟨43673258532425405816636237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29115505688283603877757491 43673258532425405816636237)
          ·
            refine ⟨16377471949659527181238589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43673258532425405816636237 16377471949659527181238589)
            ·
              refine ⟨6141551981122322692964471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16377471949659527181238589 6141551981122322692964471)
              ·
                refine ⟨9212327971683484039446707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6141551981122322692964471 9212327971683484039446707)
                ·
                  refine ⟨13818491957525226059170061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9212327971683484039446707 13818491957525226059170061)
                  ·
                    refine ⟨5181934484071959772188773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13818491957525226059170061 5181934484071959772188773)
                    ·
                      refine ⟨971612715763492457285395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5181934484071959772188773 971612715763492457285395)
                      ·
                        rfl

theorem cell23_1892209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1892209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892209 prefixEnd_1892209 := by exact prefixLift 1892209
  have htrace : WordTrace (prefixWord ++ tailWord_1892209) baseStart_1892209 baseEnd_1892209 := by
    simpa [prefixWord, tailWord_1892209, baseEnd_1892209] using wordTrace_append hprefix tailTrace_1892209
  have hstable : (prefixWord ++ tailWord_1892209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892209).length < 2 ^ (prefixWord ++ tailWord_1892209).sum := by decide
  have hdescent : baseEnd_1892209 < baseStart_1892209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892219 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 7, 4]
def baseStart_1892219 : Nat := 118140960795 + 1892219 * 2 ^ 59
def prefixEnd_1892219 : Nat := 4983230072969 + 3 ^ 40 * 1892219 * 2
def baseEnd_1892219 : Nat := 323872616856679139386783

theorem tailTrace_1892219 : CollatzResearch.WordTrace tailWord_1892219 prefixEnd_1892219 323872616856679139386783 := by
  unfold tailWord_1892219
  simp only [CollatzResearch.WordTrace]
  refine ⟨69014896731821203121807711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46009931154547468747871807 69014896731821203121807711)
  ·
    refine ⟨103522345097731804682711567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69014896731821203121807711 103522345097731804682711567)
    ·
      refine ⟨155283517646597707024067351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103522345097731804682711567 155283517646597707024067351)
      ·
        refine ⟨232925276469896560536101027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155283517646597707024067351 232925276469896560536101027)
        ·
          refine ⟨349387914704844840804151541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232925276469896560536101027 349387914704844840804151541)
          ·
            refine ⟨32755117003579203825389207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 349387914704844840804151541 32755117003579203825389207)
            ·
              refine ⟨49132675505368805738083811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32755117003579203825389207 49132675505368805738083811)
              ·
                refine ⟨73699013258053208607125717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49132675505368805738083811 73699013258053208607125717)
                ·
                  refine ⟨1727320623235622076729509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 73699013258053208607125717 1727320623235622076729509)
                  ·
                    refine ⟨323872616856679139386783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1727320623235622076729509 323872616856679139386783)
                    ·
                      rfl

theorem cell23_1892219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 4].length) (baseStart_1892219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892219 prefixEnd_1892219 := by exact prefixLift 1892219
  have htrace : WordTrace (prefixWord ++ tailWord_1892219) baseStart_1892219 baseEnd_1892219 := by
    simpa [prefixWord, tailWord_1892219, baseEnd_1892219] using wordTrace_append hprefix tailTrace_1892219
  have hstable : (prefixWord ++ tailWord_1892219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892219).length < 2 ^ (prefixWord ++ tailWord_1892219).sum := by decide
  have hdescent : baseEnd_1892219 < baseStart_1892219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892249 : List Nat := [1, 2, 1, 2, 1, 3, 2, 5, 6]
def baseStart_1892249 : Nat := 118140960795 + 1892249 * 2 ^ 59
def prefixEnd_1892249 : Nat := 4983230072969 + 3 ^ 40 * 1892249 * 2
def baseEnd_1892249 : Nat := 107959250554408033420579

theorem tailTrace_1892249 : CollatzResearch.WordTrace tailWord_1892249 prefixEnd_1892249 107959250554408033420579 := by
  unfold tailWord_1892249
  simp only [CollatzResearch.WordTrace]
  refine ⟨69015990921712518245399801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46010660614475012163599867 69015990921712518245399801)
  ·
    refine ⟨51761993191284388684049851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69015990921712518245399801 51761993191284388684049851)
    ·
      refine ⟨77642989786926583026074777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51761993191284388684049851 77642989786926583026074777)
      ·
        refine ⟨58232242340194937269556083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77642989786926583026074777 58232242340194937269556083)
        ·
          refine ⟨87348363510292405904334125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58232242340194937269556083 87348363510292405904334125)
          ·
            refine ⟨32755636316359652214125297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87348363510292405904334125 32755636316359652214125297)
            ·
              refine ⟨24566727237269739160593973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32755636316359652214125297 24566727237269739160593973)
              ·
                refine ⟨2303130678494038046305685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24566727237269739160593973 2303130678494038046305685)
                ·
                  refine ⟨107959250554408033420579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2303130678494038046305685 107959250554408033420579)
                  ·
                    rfl

theorem cell23_1892249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 5, 6].length) (baseStart_1892249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892249 prefixEnd_1892249 := by exact prefixLift 1892249
  have htrace : WordTrace (prefixWord ++ tailWord_1892249) baseStart_1892249 baseEnd_1892249 := by
    simpa [prefixWord, tailWord_1892249, baseEnd_1892249] using wordTrace_append hprefix tailTrace_1892249
  have hstable : (prefixWord ++ tailWord_1892249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892249).length < 2 ^ (prefixWord ++ tailWord_1892249).sum := by decide
  have hdescent : baseEnd_1892249 < baseStart_1892249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892259 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 3]
def baseStart_1892259 : Nat := 118140960795 + 1892259 * 2 ^ 59
def prefixEnd_1892259 : Nat := 4983230072969 + 3 ^ 40 * 1892259 * 2
def baseEnd_1892259 : Nat := 971638389796217261660165

theorem tailTrace_1892259 : CollatzResearch.WordTrace tailWord_1892259 prefixEnd_1892259 971638389796217261660165 := by
  unfold tailWord_1892259
  simp only [CollatzResearch.WordTrace]
  refine ⟨69016355651676289953263831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46010903767784193302175887 69016355651676289953263831)
  ·
    refine ⟨103524533477514434929895747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69016355651676289953263831 103524533477514434929895747)
    ·
      refine ⟨155286800216271652394843621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103524533477514434929895747 155286800216271652394843621)
      ·
        refine ⟨29116275040550934824033179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155286800216271652394843621 29116275040550934824033179)
        ·
          refine ⟨43674412560826402236049769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29116275040550934824033179 43674412560826402236049769)
          ·
            refine ⟨32755809420619801677037327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43674412560826402236049769 32755809420619801677037327)
            ·
              refine ⟨49133714130929702515555991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32755809420619801677037327 49133714130929702515555991)
              ·
                refine ⟨73700571196394553773333987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49133714130929702515555991 73700571196394553773333987)
                ·
                  refine ⟨110550856794591830660000981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73700571196394553773333987 110550856794591830660000981)
                  ·
                    refine ⟨2591035706123246031093773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 110550856794591830660000981 2591035706123246031093773)
                    ·
                      refine ⟨971638389796217261660165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591035706123246031093773 971638389796217261660165)
                      ·
                        rfl

theorem cell23_1892259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_1892259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892259 prefixEnd_1892259 := by exact prefixLift 1892259
  have htrace : WordTrace (prefixWord ++ tailWord_1892259) baseStart_1892259 baseEnd_1892259 := by
    simpa [prefixWord, tailWord_1892259, baseEnd_1892259] using wordTrace_append hprefix tailTrace_1892259
  have hstable : (prefixWord ++ tailWord_1892259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892259).length < 2 ^ (prefixWord ++ tailWord_1892259).sum := by decide
  have hdescent : baseEnd_1892259 < baseStart_1892259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892279 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 5, 5]
def baseStart_1892279 : Nat := 118140960795 + 1892279 * 2 ^ 59
def prefixEnd_1892279 : Nat := 4983230072969 + 3 ^ 40 * 1892279 * 2
def baseEnd_1892279 : Nat := 323882886469769061136691

theorem tailTrace_1892279 : CollatzResearch.WordTrace tailWord_1892279 prefixEnd_1892279 323882886469769061136691 := by
  unfold tailWord_1892279
  simp only [CollatzResearch.WordTrace]
  refine ⟨69017085111603833368991891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46011390074402555579327927 69017085111603833368991891)
  ·
    refine ⟨103525627667405750053487837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69017085111603833368991891 103525627667405750053487837)
    ·
      refine ⟨38822110375277156270057939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103525627667405750053487837 38822110375277156270057939)
      ·
        refine ⟨58233165562915734405086909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38822110375277156270057939 58233165562915734405086909)
        ·
          refine ⟨21837437086093400401907591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58233165562915734405086909 21837437086093400401907591)
          ·
            refine ⟨32756155629140100602861387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21837437086093400401907591 32756155629140100602861387)
            ·
              refine ⟨49134233443710150904292081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32756155629140100602861387 49134233443710150904292081)
              ·
                refine ⟨36850675082782613178219061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49134233443710150904292081 36850675082782613178219061)
                ·
                  refine ⟨3454750789010869985458037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36850675082782613178219061 3454750789010869985458037)
                  ·
                    refine ⟨323882886469769061136691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3454750789010869985458037 323882886469769061136691)
                    ·
                      rfl

theorem cell23_1892279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 5].length) (baseStart_1892279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892279 prefixEnd_1892279 := by exact prefixLift 1892279
  have htrace : WordTrace (prefixWord ++ tailWord_1892279) baseStart_1892279 baseEnd_1892279 := by
    simpa [prefixWord, tailWord_1892279, baseEnd_1892279] using wordTrace_append hprefix tailTrace_1892279
  have hstable : (prefixWord ++ tailWord_1892279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892279).length < 2 ^ (prefixWord ++ tailWord_1892279).sum := by decide
  have hdescent : baseEnd_1892279 < baseStart_1892279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892336 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5]
def baseStart_1892336 : Nat := 118140960795 + 1892336 * 2 ^ 59
def prefixEnd_1892336 : Nat := 4983230072969 + 3 ^ 40 * 1892336 * 2
def baseEnd_1892336 : Nat := 971677927806613460397311

theorem tailTrace_1892336 : CollatzResearch.WordTrace tailWord_1892336 prefixEnd_1892336 971677927806613460397311 := by
  unfold tailWord_1892336
  simp only [CollatzResearch.WordTrace]
  refine ⟨34509582036198666051908431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46012776048264888069211241 34509582036198666051908431)
  ·
    refine ⟨51764373054297999077862647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34509582036198666051908431 51764373054297999077862647)
    ·
      refine ⟨77646559581446998616793971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51764373054297999077862647 77646559581446998616793971)
      ·
        refine ⟨116469839372170497925190957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77646559581446998616793971 116469839372170497925190957)
        ·
          refine ⟨43676189764563936721946609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116469839372170497925190957 43676189764563936721946609)
          ·
            refine ⟨32757142323422952541459957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43676189764563936721946609 32757142323422952541459957)
            ·
              refine ⟨3070982092820901800761871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32757142323422952541459957 3070982092820901800761871)
              ·
                refine ⟨4606473139231352701142807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3070982092820901800761871 4606473139231352701142807)
                ·
                  refine ⟨6909709708847029051714211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4606473139231352701142807 6909709708847029051714211)
                  ·
                    refine ⟨10364564563270543577571317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6909709708847029051714211 10364564563270543577571317)
                    ·
                      refine ⟨971677927806613460397311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10364564563270543577571317 971677927806613460397311)
                      ·
                        rfl

theorem cell23_1892336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_1892336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892336 prefixEnd_1892336 := by exact prefixLift 1892336
  have htrace : WordTrace (prefixWord ++ tailWord_1892336) baseStart_1892336 baseEnd_1892336 := by
    simpa [prefixWord, tailWord_1892336, baseEnd_1892336] using wordTrace_append hprefix tailTrace_1892336
  have hstable : (prefixWord ++ tailWord_1892336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892336).length < 2 ^ (prefixWord ++ tailWord_1892336).sum := by decide
  have hdescent : baseEnd_1892336 < baseStart_1892336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892373 : List Nat := [1, 3, 2, 1, 5, 1, 3, 7]
def baseStart_1892373 : Nat := 118140960795 + 1892373 * 2 ^ 59
def prefixEnd_1892373 : Nat := 4983230072969 + 3 ^ 40 * 1892373 * 2
def baseEnd_1892373 : Nat := 35988775058919622801283

theorem tailTrace_1892373 : CollatzResearch.WordTrace tailWord_1892373 prefixEnd_1892373 35988775058919622801283 := by
  unfold tailWord_1892373
  simp only [CollatzResearch.WordTrace]
  refine ⟨69020513573263287422913773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46013675715508858281942515 69020513573263287422913773)
  ·
    refine ⟨25882692589973732783592665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69020513573263287422913773 25882692589973732783592665)
    ·
      refine ⟨19412019442480299587694499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25882692589973732783592665 19412019442480299587694499)
      ·
        refine ⟨29118029163720449381541749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19412019442480299587694499 29118029163720449381541749)
        ·
          refine ⟨2729815234098792129519539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29118029163720449381541749 2729815234098792129519539)
          ·
            refine ⟨4094722851148188194279309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729815234098792129519539 4094722851148188194279309)
            ·
              refine ⟨1535521069180570572854741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4094722851148188194279309 1535521069180570572854741)
              ·
                refine ⟨35988775058919622801283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1535521069180570572854741 35988775058919622801283)
                ·
                  rfl

theorem cell23_1892373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 7].length) (baseStart_1892373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892373 prefixEnd_1892373 := by exact prefixLift 1892373
  have htrace : WordTrace (prefixWord ++ tailWord_1892373) baseStart_1892373 baseEnd_1892373 := by
    simpa [prefixWord, tailWord_1892373, baseEnd_1892373] using wordTrace_append hprefix tailTrace_1892373
  have hstable : (prefixWord ++ tailWord_1892373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892373).length < 2 ^ (prefixWord ++ tailWord_1892373).sum := by decide
  have hdescent : baseEnd_1892373 < baseStart_1892373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892383 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 3]
def baseStart_1892383 : Nat := 118140960795 + 1892383 * 2 ^ 59
def prefixEnd_1892383 : Nat := 4983230072969 + 3 ^ 40 * 1892383 * 2
def baseEnd_1892383 : Nat := 971702061397374776509595

theorem tailTrace_1892383 : CollatzResearch.WordTrace tailWord_1892383 prefixEnd_1892383 971702061397374776509595 := by
  unfold tailWord_1892383
  simp only [CollatzResearch.WordTrace]
  refine ⟨69020878303227059130777803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46013918868818039420518535 69020878303227059130777803)
  ·
    refine ⟨103531317454840588696166705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69020878303227059130777803 103531317454840588696166705)
    ·
      refine ⟨77648488091130441522125029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103531317454840588696166705 77648488091130441522125029)
      ·
        refine ⟨14559091517086957785398443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77648488091130441522125029 14559091517086957785398443)
        ·
          refine ⟨21838637275630436678097665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14559091517086957785398443 21838637275630436678097665)
          ·
            refine ⟨16378977956722827508573249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21838637275630436678097665 16378977956722827508573249)
            ·
              refine ⟨12284233467542120631429937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16378977956722827508573249 12284233467542120631429937)
              ·
                refine ⟨9213175100656590473572453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12284233467542120631429937 9213175100656590473572453)
                ·
                  refine ⟨1727470331373110713794835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9213175100656590473572453 1727470331373110713794835)
                  ·
                    refine ⟨2591205497059666070692253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1727470331373110713794835 2591205497059666070692253)
                    ·
                      refine ⟨971702061397374776509595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591205497059666070692253 971702061397374776509595)
                      ·
                        rfl

theorem cell23_1892383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_1892383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892383 prefixEnd_1892383 := by exact prefixLift 1892383
  have htrace : WordTrace (prefixWord ++ tailWord_1892383) baseStart_1892383 baseEnd_1892383 := by
    simpa [prefixWord, tailWord_1892383, baseEnd_1892383] using wordTrace_append hprefix tailTrace_1892383
  have hstable : (prefixWord ++ tailWord_1892383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892383).length < 2 ^ (prefixWord ++ tailWord_1892383).sum := by decide
  have hdescent : baseEnd_1892383 < baseStart_1892383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892400 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 2, 1, 3]
def baseStart_1892400 : Nat := 118140960795 + 1892400 * 2 ^ 59
def prefixEnd_1892400 : Nat := 4983230072969 + 3 ^ 40 * 1892400 * 2
def baseEnd_1892400 : Nat := 971710790568501209997017

theorem tailTrace_1892400 : CollatzResearch.WordTrace tailWord_1892400 prefixEnd_1892400 971710790568501209997017 := by
  unfold tailWord_1892400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34510749172082735517073327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46014332229443647356097769 34510749172082735517073327)
  ·
    refine ⟨51766123758124103275609991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34510749172082735517073327 51766123758124103275609991)
    ·
      refine ⟨77649185637186154913414987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51766123758124103275609991 77649185637186154913414987)
      ·
        refine ⟨116473778455779232370122481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77649185637186154913414987 116473778455779232370122481)
        ·
          refine ⟨87355333841834424277591861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116473778455779232370122481 87355333841834424277591861)
          ·
            refine ⟨8189562547671977276024237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87355333841834424277591861 8189562547671977276024237)
            ·
              refine ⟨3071085955376991478509089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8189562547671977276024237 3071085955376991478509089)
              ·
                refine ⟨2303314466532743608881817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3071085955376991478509089 2303314466532743608881817)
                ·
                  refine ⟨1727485849899557706661363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2303314466532743608881817 1727485849899557706661363)
                  ·
                    refine ⟨2591228774849336559992045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1727485849899557706661363 2591228774849336559992045)
                    ·
                      refine ⟨971710790568501209997017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591228774849336559992045 971710790568501209997017)
                      ·
                        rfl

theorem cell23_1892400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 2, 1, 3].length) (baseStart_1892400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892400 prefixEnd_1892400 := by exact prefixLift 1892400
  have htrace : WordTrace (prefixWord ++ tailWord_1892400) baseStart_1892400 baseEnd_1892400 := by
    simpa [prefixWord, tailWord_1892400, baseEnd_1892400] using wordTrace_append hprefix tailTrace_1892400
  have hstable : (prefixWord ++ tailWord_1892400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892400).length < 2 ^ (prefixWord ++ tailWord_1892400).sum := by decide
  have hdescent : baseEnd_1892400 < baseStart_1892400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892416 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 2, 6]
def baseStart_1892416 : Nat := 118140960795 + 1892416 * 2 ^ 59
def prefixEnd_1892416 : Nat := 4983230072969 + 3 ^ 40 * 1892416 * 2
def baseEnd_1892416 : Nat := 323906335419657715798981

theorem tailTrace_1892416 : CollatzResearch.WordTrace tailWord_1892416 prefixEnd_1892416 323906335419657715798981 := by
  unfold tailWord_1892416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34511040956053752883364551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46014721274738337177819401 34511040956053752883364551)
  ·
    refine ⟨51766561434080629325046827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34511040956053752883364551 51766561434080629325046827)
    ·
      refine ⟨77649842151120943987570241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51766561434080629325046827 77649842151120943987570241)
      ·
        refine ⟨58237381613340707990677681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77649842151120943987570241 58237381613340707990677681)
        ·
          refine ⟨43678036210005530993008261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58237381613340707990677681 43678036210005530993008261)
          ·
            refine ⟨8189631789376037061189049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43678036210005530993008261 8189631789376037061189049)
            ·
              refine ⟨6142223842032027795891787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8189631789376037061189049 6142223842032027795891787)
              ·
                refine ⟨9213335763048041693837681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6142223842032027795891787 9213335763048041693837681)
                ·
                  refine ⟨6910001822286031270378261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9213335763048041693837681 6910001822286031270378261)
                  ·
                    refine ⟨323906335419657715798981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6910001822286031270378261 323906335419657715798981)
                    ·
                      rfl

theorem cell23_1892416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 6].length) (baseStart_1892416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892416 prefixEnd_1892416 := by exact prefixLift 1892416
  have htrace : WordTrace (prefixWord ++ tailWord_1892416) baseStart_1892416 baseEnd_1892416 := by
    simpa [prefixWord, tailWord_1892416, baseEnd_1892416] using wordTrace_append hprefix tailTrace_1892416
  have hstable : (prefixWord ++ tailWord_1892416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892416).length < 2 ^ (prefixWord ++ tailWord_1892416).sum := by decide
  have hdescent : baseEnd_1892416 < baseStart_1892416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892426 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5]
def baseStart_1892426 : Nat := 118140960795 + 1892426 * 2 ^ 59
def prefixEnd_1892426 : Nat := 4983230072969 + 3 ^ 40 * 1892426 * 2
def baseEnd_1892426 : Nat := 971724141065518108271897

theorem tailTrace_1892426 : CollatzResearch.WordTrace tailWord_1892426 prefixEnd_1892426 971724141065518108271897 := by
  unfold tailWord_1892426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17255611660517819368648283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46014964428047518316395421 17255611660517819368648283)
  ·
    refine ⟨25883417490776729052972425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17255611660517819368648283 25883417490776729052972425)
    ·
      refine ⟨19412563118082546789729319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25883417490776729052972425 19412563118082546789729319)
      ·
        refine ⟨29118844677123820184593979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19412563118082546789729319 29118844677123820184593979)
        ·
          refine ⟨43678267015685730276890969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29118844677123820184593979 43678267015685730276890969)
          ·
            refine ⟨32758700261764297707668227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43678267015685730276890969 32758700261764297707668227)
            ·
              refine ⟨49138050392646446561502341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32758700261764297707668227 49138050392646446561502341)
              ·
                refine ⟨9213384448621208730281689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49138050392646446561502341 9213384448621208730281689)
                ·
                  refine ⟨6910038336465906547711267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9213384448621208730281689 6910038336465906547711267)
                  ·
                    refine ⟨10365057504698859821566901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910038336465906547711267 10365057504698859821566901)
                    ·
                      refine ⟨971724141065518108271897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10365057504698859821566901 971724141065518108271897)
                      ·
                        rfl

theorem cell23_1892426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_1892426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892426 prefixEnd_1892426 := by exact prefixLift 1892426
  have htrace : WordTrace (prefixWord ++ tailWord_1892426) baseStart_1892426 baseEnd_1892426 := by
    simpa [prefixWord, tailWord_1892426, baseEnd_1892426] using wordTrace_append hprefix tailTrace_1892426
  have hstable : (prefixWord ++ tailWord_1892426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892426).length < 2 ^ (prefixWord ++ tailWord_1892426).sum := by decide
  have hdescent : baseEnd_1892426 < baseStart_1892426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892440 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 4, 2, 2]
def baseStart_1892440 : Nat := 118140960795 + 1892440 * 2 ^ 59
def prefixEnd_1892440 : Nat := 4983230072969 + 3 ^ 40 * 1892440 * 2
def baseEnd_1892440 : Nat := 971731329794681053496833

theorem tailTrace_1892440 : CollatzResearch.WordTrace tailWord_1892440 prefixEnd_1892440 971731329794681053496833 := by
  unfold tailWord_1892440
  simp only [CollatzResearch.WordTrace]
  refine ⟨34511478632010278932801387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46015304842680371910401849 34511478632010278932801387)
  ·
    refine ⟨51767217948015418399202081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34511478632010278932801387 51767217948015418399202081)
    ·
      refine ⟨38825413461011563799401561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51767217948015418399202081 38825413461011563799401561)
      ·
        refine ⟨29119060095758672849551171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38825413461011563799401561 29119060095758672849551171)
        ·
          refine ⟨43678590143638009274326757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29119060095758672849551171 43678590143638009274326757)
          ·
            refine ⟨8189735651932126738936267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43678590143638009274326757 8189735651932126738936267)
            ·
              refine ⟨12284603477898190108404401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8189735651932126738936267 12284603477898190108404401)
              ·
                refine ⟨9213452608423642581303301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12284603477898190108404401 9213452608423642581303301)
                ·
                  refine ⟨1727522364079432983994369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9213452608423642581303301 1727522364079432983994369)
                  ·
                    refine ⟨1295641773059574737995777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727522364079432983994369 1295641773059574737995777)
                    ·
                      refine ⟨971731329794681053496833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295641773059574737995777 971731329794681053496833)
                      ·
                        rfl

theorem cell23_1892440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_1892440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892440 prefixEnd_1892440 := by exact prefixLift 1892440
  have htrace : WordTrace (prefixWord ++ tailWord_1892440) baseStart_1892440 baseEnd_1892440 := by
    simpa [prefixWord, tailWord_1892440, baseEnd_1892440] using wordTrace_append hprefix tailTrace_1892440
  have hstable : (prefixWord ++ tailWord_1892440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892440).length < 2 ^ (prefixWord ++ tailWord_1892440).sum := by decide
  have hdescent : baseEnd_1892440 < baseStart_1892440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892463 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 7]
def baseStart_1892463 : Nat := 118140960795 + 1892463 * 2 ^ 59
def prefixEnd_1892463 : Nat := 4983230072969 + 3 ^ 40 * 1892463 * 2
def baseEnd_1892463 : Nat := 107971459983303829278803

theorem tailTrace_1892463 : CollatzResearch.WordTrace tailWord_1892463 prefixEnd_1892463 107971459983303829278803 := by
  unfold tailWord_1892463
  simp only [CollatzResearch.WordTrace]
  refine ⟨69023796142937232793690043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46015864095291488529126695 69023796142937232793690043)
  ·
    refine ⟨103535694214405849190535065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69023796142937232793690043 103535694214405849190535065)
    ·
      refine ⟨77651770660804386892901299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103535694214405849190535065 77651770660804386892901299)
      ·
        refine ⟨116477655991206580339351949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77651770660804386892901299 116477655991206580339351949)
        ·
          refine ⟨43679120996702467627256981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116477655991206580339351949 43679120996702467627256981)
          ·
            refine ⟨2047458796720428170027671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43679120996702467627256981 2047458796720428170027671)
            ·
              refine ⟨3071188195080642255041507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2047458796720428170027671 3071188195080642255041507)
              ·
                refine ⟨4606782292620963382562261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071188195080642255041507 4606782292620963382562261)
                ·
                  refine ⟨107971459983303829278803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4606782292620963382562261 107971459983303829278803)
                  ·
                    rfl

theorem cell23_1892463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 7].length) (baseStart_1892463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892463 prefixEnd_1892463 := by exact prefixLift 1892463
  have htrace : WordTrace (prefixWord ++ tailWord_1892463) baseStart_1892463 baseEnd_1892463 := by
    simpa [prefixWord, tailWord_1892463, baseEnd_1892463] using wordTrace_append hprefix tailTrace_1892463
  have hstable : (prefixWord ++ tailWord_1892463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892463).length < 2 ^ (prefixWord ++ tailWord_1892463).sum := by decide
  have hdescent : baseEnd_1892463 < baseStart_1892463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892514 : List Nat := [3, 3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1892514 : Nat := 118140960795 + 1892514 * 2 ^ 59
def prefixEnd_1892514 : Nat := 4983230072969 + 3 ^ 40 * 1892514 * 2
def baseEnd_1892514 : Nat := 107974369707012640441277

theorem tailTrace_1892514 : CollatzResearch.WordTrace tailWord_1892514 prefixEnd_1892514 107974369707012640441277 := by
  unfold tailWord_1892514
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256414066438117125949149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46017104177168312335864397 17256414066438117125949149)
  ·
    refine ⟨6471155274914293922230931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17256414066438117125949149 6471155274914293922230931)
    ·
      refine ⟨9706732912371440883346397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6471155274914293922230931 9706732912371440883346397)
      ·
        refine ⟨3640024842139290331254899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9706732912371440883346397 3640024842139290331254899)
        ·
          refine ⟨5460037263208935496882349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640024842139290331254899 5460037263208935496882349)
          ·
            refine ⟨2047513973703350811330881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5460037263208935496882349 2047513973703350811330881)
            ·
              refine ⟨1535635480277513108498161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047513973703350811330881 1535635480277513108498161)
              ·
                refine ⟨1151726610208134831373621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535635480277513108498161 1151726610208134831373621)
                ·
                  refine ⟨107974369707012640441277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1151726610208134831373621 107974369707012640441277)
                  ·
                    rfl

theorem cell23_1892514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1892514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892514 prefixEnd_1892514 := by exact prefixLift 1892514
  have htrace : WordTrace (prefixWord ++ tailWord_1892514) baseStart_1892514 baseEnd_1892514 := by
    simpa [prefixWord, tailWord_1892514, baseEnd_1892514] using wordTrace_append hprefix tailTrace_1892514
  have hstable : (prefixWord ++ tailWord_1892514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892514).length < 2 ^ (prefixWord ++ tailWord_1892514).sum := by decide
  have hdescent : baseEnd_1892514 < baseStart_1892514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892530 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_1892530 : Nat := 118140960795 + 1892530 * 2 ^ 59
def prefixEnd_1892530 : Nat := 4983230072969 + 3 ^ 40 * 1892530 * 2
def baseEnd_1892530 : Nat := 971777543053585701371419

theorem tailTrace_1892530 : CollatzResearch.WordTrace tailWord_1892530 prefixEnd_1892530 971777543053585701371419 := by
  unfold tailWord_1892530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17256559958423625809094761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46017493222463002157586029 17256559958423625809094761)
  ·
    refine ⟨12942419968817719356821071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17256559958423625809094761 12942419968817719356821071)
    ·
      refine ⟨19413629953226579035231607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12942419968817719356821071 19413629953226579035231607)
      ·
        refine ⟨29120444929839868552847411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19413629953226579035231607 29120444929839868552847411)
        ·
          refine ⟨43680667394759802829271117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29120444929839868552847411 43680667394759802829271117)
          ·
            refine ⟨16380250273034926060976669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43680667394759802829271117 16380250273034926060976669)
            ·
              refine ⟨6142593852388097272866251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16380250273034926060976669 6142593852388097272866251)
              ·
                refine ⟨9213890778582145909299377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6142593852388097272866251 9213890778582145909299377)
                ·
                  refine ⟨6910418083936609431974533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9213890778582145909299377 6910418083936609431974533)
                  ·
                    refine ⟨1295703390738114268495225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6910418083936609431974533 1295703390738114268495225)
                    ·
                      refine ⟨971777543053585701371419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295703390738114268495225 971777543053585701371419)
                      ·
                        rfl

theorem cell23_1892530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_1892530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892530 prefixEnd_1892530 := by exact prefixLift 1892530
  have htrace : WordTrace (prefixWord ++ tailWord_1892530) baseStart_1892530 baseEnd_1892530 := by
    simpa [prefixWord, tailWord_1892530, baseEnd_1892530] using wordTrace_append hprefix tailTrace_1892530
  have hstable : (prefixWord ++ tailWord_1892530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892530).length < 2 ^ (prefixWord ++ tailWord_1892530).sum := by decide
  have hdescent : baseEnd_1892530 < baseStart_1892530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892620 : List Nat := [2, 2, 1, 2, 2, 2, 1, 5, 1, 1, 4]
def baseStart_1892620 : Nat := 118140960795 + 1892620 * 2 ^ 59
def prefixEnd_1892620 : Nat := 4983230072969 + 3 ^ 40 * 1892620 * 2
def baseEnd_1892620 : Nat := 971823756312490349246005

theorem tailTrace_1892620 : CollatzResearch.WordTrace tailWord_1892620 prefixEnd_1892620 971823756312490349246005 := by
  unfold tailWord_1892620
  simp only [CollatzResearch.WordTrace]
  refine ⟨34514761201684224303577657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46019681602245632404770209 34514761201684224303577657)
  ·
    refine ⟨25886070901263168227683243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34514761201684224303577657 25886070901263168227683243)
    ·
      refine ⟨38829106351894752341524865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25886070901263168227683243 38829106351894752341524865)
      ·
        refine ⟨29121829763921064256143649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38829106351894752341524865 29121829763921064256143649)
        ·
          refine ⟨21841372322940798192107737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29121829763921064256143649 21841372322940798192107737)
          ·
            refine ⟨16381029242205598644080803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21841372322940798192107737 16381029242205598644080803)
            ·
              refine ⟨24571543863308397966121205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16381029242205598644080803 24571543863308397966121205)
              ·
                refine ⟨2303582237185162309323863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24571543863308397966121205 2303582237185162309323863)
                ·
                  refine ⟨3455373355777743463985795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303582237185162309323863 3455373355777743463985795)
                  ·
                    refine ⟨5183060033666615195978693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3455373355777743463985795 5183060033666615195978693)
                    ·
                      refine ⟨971823756312490349246005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5183060033666615195978693 971823756312490349246005)
                      ·
                        rfl

theorem cell23_1892620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_1892620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892620 prefixEnd_1892620 := by exact prefixLift 1892620
  have htrace : WordTrace (prefixWord ++ tailWord_1892620) baseStart_1892620 baseEnd_1892620 := by
    simpa [prefixWord, tailWord_1892620, baseEnd_1892620] using wordTrace_append hprefix tailTrace_1892620
  have hstable : (prefixWord ++ tailWord_1892620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892620).length < 2 ^ (prefixWord ++ tailWord_1892620).sum := by decide
  have hdescent : baseEnd_1892620 < baseStart_1892620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892631 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 1, 1, 3]
def baseStart_1892631 : Nat := 118140960795 + 1892631 * 2 ^ 59
def prefixEnd_1892631 : Nat := 4983230072969 + 3 ^ 40 * 1892631 * 2
def baseEnd_1892631 : Nat := 971829404599689806208455

theorem tailTrace_1892631 : CollatzResearch.WordTrace tailWord_1892631 prefixEnd_1892631 971829404599689806208455 := by
  unfold tailWord_1892631
  simp only [CollatzResearch.WordTrace]
  refine ⟨69029923606328597485805747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46019949070885731657203831 69029923606328597485805747)
  ·
    refine ⟨103544885409492896228708621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69029923606328597485805747 103544885409492896228708621)
    ·
      refine ⟨38829332028559836085765733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103544885409492896228708621 38829332028559836085765733)
      ·
        refine ⟨7280499755354969266081075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38829332028559836085765733 7280499755354969266081075)
        ·
          refine ⟨10920749633032453899121613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280499755354969266081075 10920749633032453899121613)
          ·
            refine ⟨4095281112387170212170605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10920749633032453899121613 4095281112387170212170605)
            ·
              refine ⟨1535730417145188829563977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4095281112387170212170605 1535730417145188829563977)
              ·
                refine ⟨1151797812858891622172983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535730417145188829563977 1151797812858891622172983)
                ·
                  refine ⟨1727696719288337433259475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151797812858891622172983 1727696719288337433259475)
                  ·
                    refine ⟨2591545078932506149889213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1727696719288337433259475 2591545078932506149889213)
                    ·
                      refine ⟨971829404599689806208455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591545078932506149889213 971829404599689806208455)
                      ·
                        rfl

theorem cell23_1892631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_1892631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892631 prefixEnd_1892631 := by exact prefixLift 1892631
  have htrace : WordTrace (prefixWord ++ tailWord_1892631) baseStart_1892631 baseEnd_1892631 := by
    simpa [prefixWord, tailWord_1892631, baseEnd_1892631] using wordTrace_append hprefix tailTrace_1892631
  have hstable : (prefixWord ++ tailWord_1892631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892631).length < 2 ^ (prefixWord ++ tailWord_1892631).sum := by decide
  have hdescent : baseEnd_1892631 < baseStart_1892631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892640 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1892640 : Nat := 118140960795 + 1892640 * 2 ^ 59
def prefixEnd_1892640 : Nat := 4983230072969 + 3 ^ 40 * 1892640 * 2
def baseEnd_1892640 : Nat := 971834025925580270995913

theorem tailTrace_1892640 : CollatzResearch.WordTrace tailWord_1892640 prefixEnd_1892640 971834025925580270995913 := by
  unfold tailWord_1892640
  simp only [CollatzResearch.WordTrace]
  refine ⟨34515125931647996011441687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46020167908863994681922249 34515125931647996011441687)
  ·
    refine ⟨51772688897471994017162531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34515125931647996011441687 51772688897471994017162531)
    ·
      refine ⟨77659033346207991025743797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51772688897471994017162531 77659033346207991025743797)
      ·
        refine ⟨7280534376206999158663481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77659033346207991025743797 7280534376206999158663481)
        ·
          refine ⟨5460400782155249368997611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7280534376206999158663481 5460400782155249368997611)
          ·
            refine ⟨8190601173232874053496417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460400782155249368997611 8190601173232874053496417)
            ·
              refine ⟨6142950879924655540122313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8190601173232874053496417 6142950879924655540122313)
              ·
                refine ⟨4607213159943491655091735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6142950879924655540122313 4607213159943491655091735)
                ·
                  refine ⟨6910819739915237482637603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607213159943491655091735 6910819739915237482637603)
                  ·
                    refine ⟨10366229609872856223956405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6910819739915237482637603 10366229609872856223956405)
                    ·
                      refine ⟨971834025925580270995913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10366229609872856223956405 971834025925580270995913)
                      ·
                        rfl

theorem cell23_1892640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1892640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892640 prefixEnd_1892640 := by exact prefixLift 1892640
  have htrace : WordTrace (prefixWord ++ tailWord_1892640) baseStart_1892640 baseEnd_1892640 := by
    simpa [prefixWord, tailWord_1892640, baseEnd_1892640] using wordTrace_append hprefix tailTrace_1892640
  have hstable : (prefixWord ++ tailWord_1892640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892640).length < 2 ^ (prefixWord ++ tailWord_1892640).sum := by decide
  have hdescent : baseEnd_1892640 < baseStart_1892640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892643 : List Nat := [1, 1, 1, 4, 2, 2, 4, 8]
def baseStart_1892643 : Nat := 118140960795 + 1892643 * 2 ^ 59
def prefixEnd_1892643 : Nat := 4983230072969 + 3 ^ 40 * 1892643 * 2
def baseEnd_1892643 : Nat := 35993909865464583676237

theorem tailTrace_1892643 : CollatzResearch.WordTrace tailWord_1892643 prefixEnd_1892643 35993909865464583676237 := by
  unfold tailWord_1892643
  simp only [CollatzResearch.WordTrace]
  refine ⟨69030361282285123535242583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46020240854856749023495055 69030361282285123535242583)
  ·
    refine ⟨103545541923427685302863875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69030361282285123535242583 103545541923427685302863875)
    ·
      refine ⟨155318312885141527954295813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103545541923427685302863875 155318312885141527954295813)
      ·
        refine ⟨29122183665964036491430465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 155318312885141527954295813 29122183665964036491430465)
        ·
          refine ⟨21841637749473027368572849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29122183665964036491430465 21841637749473027368572849)
          ·
            refine ⟨16381228312104770526429637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21841637749473027368572849 16381228312104770526429637)
            ·
              refine ⟨3071480308519644473705557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16381228312104770526429637 3071480308519644473705557)
              ·
                refine ⟨35993909865464583676237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3071480308519644473705557 35993909865464583676237)
                ·
                  rfl

theorem cell23_1892643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 8].length) (baseStart_1892643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892643 prefixEnd_1892643 := by exact prefixLift 1892643
  have htrace : WordTrace (prefixWord ++ tailWord_1892643) baseStart_1892643 baseEnd_1892643 := by
    simpa [prefixWord, tailWord_1892643, baseEnd_1892643] using wordTrace_append hprefix tailTrace_1892643
  have hstable : (prefixWord ++ tailWord_1892643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892643).length < 2 ^ (prefixWord ++ tailWord_1892643).sum := by decide
  have hdescent : baseEnd_1892643 < baseStart_1892643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892654 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1892654 : Nat := 118140960795 + 1892654 * 2 ^ 59
def prefixEnd_1892654 : Nat := 4983230072969 + 3 ^ 40 * 1892654 * 2
def baseEnd_1892654 : Nat := 971841214654743216220849

theorem tailTrace_1892654 : CollatzResearch.WordTrace tailWord_1892654 prefixEnd_1892654 971841214654743216220849 := by
  unfold tailWord_1892654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8628845310655659051736627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46020508323496848275928677 8628845310655659051736627)
  ·
    refine ⟨12943267965983488577604941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8628845310655659051736627 12943267965983488577604941)
    ·
      refine ⟨4853725487243808216601853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12943267965983488577604941 4853725487243808216601853)
      ·
        refine ⟨1820147057716428081225695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4853725487243808216601853 1820147057716428081225695)
        ·
          refine ⟨2730220586574642121838543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820147057716428081225695 2730220586574642121838543)
          ·
            refine ⟨4095330879861963182757815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730220586574642121838543 4095330879861963182757815)
            ·
              refine ⟨6142996319792944774136723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095330879861963182757815 6142996319792944774136723)
              ·
                refine ⟨9214494479689417161205085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6142996319792944774136723 9214494479689417161205085)
                ·
                  refine ⟨3455435429883531435451907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9214494479689417161205085 3455435429883531435451907)
                  ·
                    refine ⟨5183153144825297153177861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3455435429883531435451907 5183153144825297153177861)
                    ·
                      refine ⟨971841214654743216220849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5183153144825297153177861 971841214654743216220849)
                      ·
                        rfl

theorem cell23_1892654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1892654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892654 prefixEnd_1892654 := by exact prefixLift 1892654
  have htrace : WordTrace (prefixWord ++ tailWord_1892654) baseStart_1892654 baseEnd_1892654 := by
    simpa [prefixWord, tailWord_1892654, baseEnd_1892654] using wordTrace_append hprefix tailTrace_1892654
  have hstable : (prefixWord ++ tailWord_1892654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892654).length < 2 ^ (prefixWord ++ tailWord_1892654).sum := by decide
  have hdescent : baseEnd_1892654 < baseStart_1892654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892657 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_1892657 : Nat := 118140960795 + 1892657 * 2 ^ 59
def prefixEnd_1892657 : Nat := 4983230072969 + 3 ^ 40 * 1892657 * 2
def baseEnd_1892657 : Nat := 971842755096706704483335

theorem tailTrace_1892657 : CollatzResearch.WordTrace tailWord_1892657 prefixEnd_1892657 971842755096706704483335 := by
  unfold tailWord_1892657
  simp only [CollatzResearch.WordTrace]
  refine ⟨69030871904234403926252225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46020581269489602617501483 69030871904234403926252225)
  ·
    refine ⟨51773153928175802944689169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69030871904234403926252225 51773153928175802944689169)
    ·
      refine ⟨38829865446131852208516877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51773153928175802944689169 38829865446131852208516877)
      ·
        refine ⟨14561199542299444578193829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38829865446131852208516877 14561199542299444578193829)
        ·
          refine ⟨2730224914181145858411343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14561199542299444578193829 2730224914181145858411343)
          ·
            refine ⟨4095337371271718787617015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730224914181145858411343 4095337371271718787617015)
            ·
              refine ⟨6143006056907578181425523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095337371271718787617015 6143006056907578181425523)
              ·
                refine ⟨9214509085361367272138285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143006056907578181425523 9214509085361367272138285)
                ·
                  refine ⟨3455440907010512727051857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9214509085361367272138285 3455440907010512727051857)
                  ·
                    refine ⟨2591580680257884545288893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3455440907010512727051857 2591580680257884545288893)
                    ·
                      refine ⟨971842755096706704483335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591580680257884545288893 971842755096706704483335)
                      ·
                        rfl

theorem cell23_1892657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_1892657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892657 prefixEnd_1892657 := by exact prefixLift 1892657
  have htrace : WordTrace (prefixWord ++ tailWord_1892657) baseStart_1892657 baseEnd_1892657 := by
    simpa [prefixWord, tailWord_1892657, baseEnd_1892657] using wordTrace_append hprefix tailTrace_1892657
  have hstable : (prefixWord ++ tailWord_1892657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892657).length < 2 ^ (prefixWord ++ tailWord_1892657).sum := by decide
  have hdescent : baseEnd_1892657 < baseStart_1892657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892660 : List Nat := [2, 5, 1, 1, 1, 2, 2, 9]
def baseStart_1892660 : Nat := 118140960795 + 1892660 * 2 ^ 59
def prefixEnd_1892660 : Nat := 4983230072969 + 3 ^ 40 * 1892660 * 2
def baseEnd_1892660 : Nat := 35994233168098896027623

theorem tailTrace_1892660 : CollatzResearch.WordTrace tailWord_1892660 prefixEnd_1892660 35994233168098896027623 := by
  unfold tailWord_1892660
  simp only [CollatzResearch.WordTrace]
  refine ⟨34515490661611767719305717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46020654215482356959074289 34515490661611767719305717)
  ·
    refine ⟨3235827249526103223684911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34515490661611767719305717 3235827249526103223684911)
    ·
      refine ⟨4853740874289154835527367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3235827249526103223684911 4853740874289154835527367)
      ·
        refine ⟨7280611311433732253291051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4853740874289154835527367 7280611311433732253291051)
        ·
          refine ⟨10920916967150598379936577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280611311433732253291051 10920916967150598379936577)
          ·
            refine ⟨8190687725362948784952433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10920916967150598379936577 8190687725362948784952433)
            ·
              refine ⟨6143015794022211588714325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8190687725362948784952433 6143015794022211588714325)
              ·
                refine ⟨35994233168098896027623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6143015794022211588714325 35994233168098896027623)
                ·
                  rfl

theorem cell23_1892660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 9].length) (baseStart_1892660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892660 prefixEnd_1892660 := by exact prefixLift 1892660
  have htrace : WordTrace (prefixWord ++ tailWord_1892660) baseStart_1892660 baseEnd_1892660 := by
    simpa [prefixWord, tailWord_1892660, baseEnd_1892660] using wordTrace_append hprefix tailTrace_1892660
  have hstable : (prefixWord ++ tailWord_1892660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892660).length < 2 ^ (prefixWord ++ tailWord_1892660).sum := by decide
  have hdescent : baseEnd_1892660 < baseStart_1892660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892688 : List Nat := [2, 1, 1, 1, 1, 8, 2, 2, 1, 2, 2]
def baseStart_1892688 : Nat := 118140960795 + 1892688 * 2 ^ 59
def prefixEnd_1892688 : Nat := 4983230072969 + 3 ^ 40 * 1892688 * 2
def baseEnd_1892688 : Nat := 971858672996996083195693

theorem tailTrace_1892688 : CollatzResearch.WordTrace tailWord_1892688 prefixEnd_1892688 971858672996996083195693 := by
  unfold tailWord_1892688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34516001283561048110315359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46021335044748064147087145 34516001283561048110315359)
  ·
    refine ⟨51774001925341572165473039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34516001283561048110315359 51774001925341572165473039)
    ·
      refine ⟨77661002888012358248209559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51774001925341572165473039 77661002888012358248209559)
      ·
        refine ⟨116491504332018537372314339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77661002888012358248209559 116491504332018537372314339)
        ·
          refine ⟨174737256498027806058471509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116491504332018537372314339 174737256498027806058471509)
          ·
            refine ⟨2047702224586263352247713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 174737256498027806058471509 2047702224586263352247713)
            ·
              refine ⟨1535776668439697514185785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047702224586263352247713 1535776668439697514185785)
              ·
                refine ⟨1151832501329773135639339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1535776668439697514185785 1151832501329773135639339)
                ·
                  refine ⟨1727748751994659703459009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151832501329773135639339 1727748751994659703459009)
                  ·
                    refine ⟨1295811563995994777594257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727748751994659703459009 1295811563995994777594257)
                    ·
                      refine ⟨971858672996996083195693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295811563995994777594257 971858672996996083195693)
                      ·
                        rfl

theorem cell23_1892688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 1, 2, 2].length) (baseStart_1892688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892688 prefixEnd_1892688 := by exact prefixLift 1892688
  have htrace : WordTrace (prefixWord ++ tailWord_1892688) baseStart_1892688 baseEnd_1892688 := by
    simpa [prefixWord, tailWord_1892688, baseEnd_1892688] using wordTrace_append hprefix tailTrace_1892688
  have hstable : (prefixWord ++ tailWord_1892688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892688).length < 2 ^ (prefixWord ++ tailWord_1892688).sum := by decide
  have hdescent : baseEnd_1892688 < baseStart_1892688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892703 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 8]
def baseStart_1892703 : Nat := 118140960795 + 1892703 * 2 ^ 59
def prefixEnd_1892703 : Nat := 4983230072969 + 3 ^ 40 * 1892703 * 2
def baseEnd_1892703 : Nat := 323955458402271174836041

theorem tailTrace_1892703 : CollatzResearch.WordTrace tailWord_1892703 prefixEnd_1892703 323955458402271174836041 := by
  unfold tailWord_1892703
  simp only [CollatzResearch.WordTrace]
  refine ⟨69032549662067753782426763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46021699774711835854951175 69032549662067753782426763)
  ·
    refine ⟨103548824493101630673640145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69032549662067753782426763 103548824493101630673640145)
    ·
      refine ⟨77661618369826223005230109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103548824493101630673640145 77661618369826223005230109)
      ·
        refine ⟨29123106888684833626961291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77661618369826223005230109 29123106888684833626961291)
        ·
          refine ⟨43684660333027250440441937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29123106888684833626961291 43684660333027250440441937)
          ·
            refine ⟨32763495249770437830331453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43684660333027250440441937 32763495249770437830331453)
            ·
              refine ⟨12286310718663914186374295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32763495249770437830331453 12286310718663914186374295)
              ·
                refine ⟨18429466077995871279561443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12286310718663914186374295 18429466077995871279561443)
                ·
                  refine ⟨27644199116993806919342165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18429466077995871279561443 27644199116993806919342165)
                  ·
                    refine ⟨323955458402271174836041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27644199116993806919342165 323955458402271174836041)
                    ·
                      rfl

theorem cell23_1892703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 8].length) (baseStart_1892703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892703 prefixEnd_1892703 := by exact prefixLift 1892703
  have htrace : WordTrace (prefixWord ++ tailWord_1892703) baseStart_1892703 baseEnd_1892703 := by
    simpa [prefixWord, tailWord_1892703, baseEnd_1892703] using wordTrace_append hprefix tailTrace_1892703
  have hstable : (prefixWord ++ tailWord_1892703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892703).length < 2 ^ (prefixWord ++ tailWord_1892703).sum := by decide
  have hdescent : baseEnd_1892703 < baseStart_1892703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892714 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2]
def baseStart_1892714 : Nat := 118140960795 + 1892714 * 2 ^ 59
def prefixEnd_1892714 : Nat := 4983230072969 + 3 ^ 40 * 1892714 * 2
def baseEnd_1892714 : Nat := 971872023494012981470573

theorem tailTrace_1892714 : CollatzResearch.WordTrace tailWord_1892714 prefixEnd_1892714 971872023494012981470573 := by
  unfold tailWord_1892714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17258237716256975665269299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46021967243351935107384797 17258237716256975665269299)
  ·
    refine ⟨25887356574385463497903949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17258237716256975665269299 25887356574385463497903949)
    ·
      refine ⟨9707758715394548811713981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25887356574385463497903949 9707758715394548811713981)
      ·
        refine ⟨3640409518272955804392743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9707758715394548811713981 3640409518272955804392743)
        ·
          refine ⟨5460614277409433706589115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640409518272955804392743 5460614277409433706589115)
          ·
            refine ⟨8190921416114150559883673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460614277409433706589115 8190921416114150559883673)
            ·
              refine ⟨6143191062085612919912755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8190921416114150559883673 6143191062085612919912755)
              ·
                refine ⟨9214786593128419379869133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143191062085612919912755 9214786593128419379869133)
                ·
                  refine ⟨3455544972423157267450925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9214786593128419379869133 3455544972423157267450925)
                  ·
                    refine ⟨1295829364658683975294097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3455544972423157267450925 1295829364658683975294097)
                    ·
                      refine ⟨971872023494012981470573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295829364658683975294097 971872023494012981470573)
                      ·
                        rfl

theorem cell23_1892714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_1892714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892714 prefixEnd_1892714 := by exact prefixLift 1892714
  have htrace : WordTrace (prefixWord ++ tailWord_1892714) baseStart_1892714 baseEnd_1892714 := by
    simpa [prefixWord, tailWord_1892714, baseEnd_1892714] using wordTrace_append hprefix tailTrace_1892714
  have hstable : (prefixWord ++ tailWord_1892714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892714).length < 2 ^ (prefixWord ++ tailWord_1892714).sum := by decide
  have hdescent : baseEnd_1892714 < baseStart_1892714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892731 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 1, 3, 2]
def baseStart_1892731 : Nat := 118140960795 + 1892731 * 2 ^ 59
def prefixEnd_1892731 : Nat := 4983230072969 + 3 ^ 40 * 1892731 * 2
def baseEnd_1892731 : Nat := 971880752665139414957995

theorem tailTrace_1892731 : CollatzResearch.WordTrace tailWord_1892731 prefixEnd_1892731 971880752665139414957995 := by
  unfold tailWord_1892731
  simp only [CollatzResearch.WordTrace]
  refine ⟨69033570905966314564446047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46022380603977543042964031 69033570905966314564446047)
  ·
    refine ⟨103550356358949471846669071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69033570905966314564446047 103550356358949471846669071)
    ·
      refine ⟨155325534538424207770003607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103550356358949471846669071 155325534538424207770003607)
      ·
        refine ⟨232988301807636311655005411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155325534538424207770003607 232988301807636311655005411)
        ·
          refine ⟨349482452711454467482508117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232988301807636311655005411 349482452711454467482508117)
          ·
            refine ⟨2047748746356178520405321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 349482452711454467482508117 2047748746356178520405321)
            ·
              refine ⟨1535811559767133890303991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2047748746356178520405321 1535811559767133890303991)
              ·
                refine ⟨2303717339650700835455987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535811559767133890303991 2303717339650700835455987)
                ·
                  refine ⟨3455576009476051253183981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303717339650700835455987 3455576009476051253183981)
                  ·
                    refine ⟨1295841003553519219943993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3455576009476051253183981 1295841003553519219943993)
                    ·
                      refine ⟨971880752665139414957995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295841003553519219943993 971880752665139414957995)
                      ·
                        rfl

theorem cell23_1892731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 1, 3, 2].length) (baseStart_1892731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892731 prefixEnd_1892731 := by exact prefixLift 1892731
  have htrace : WordTrace (prefixWord ++ tailWord_1892731) baseStart_1892731 baseEnd_1892731 := by
    simpa [prefixWord, tailWord_1892731, baseEnd_1892731] using wordTrace_append hprefix tailTrace_1892731
  have hstable : (prefixWord ++ tailWord_1892731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892731).length < 2 ^ (prefixWord ++ tailWord_1892731).sum := by decide
  have hdescent : baseEnd_1892731 < baseStart_1892731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892740 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1892740 : Nat := 118140960795 + 1892740 * 2 ^ 59
def prefixEnd_1892740 : Nat := 4983230072969 + 3 ^ 40 * 1892740 * 2
def baseEnd_1892740 : Nat := 971885373991029879745453

theorem tailTrace_1892740 : CollatzResearch.WordTrace tailWord_1892740 prefixEnd_1892740 971885373991029879745453 := by
  unfold tailWord_1892740
  simp only [CollatzResearch.WordTrace]
  refine ⟨34516949581466854550761837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46022599441955806067682449 34516949581466854550761837)
  ·
    refine ⟨12943856093050070456535689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34516949581466854550761837 12943856093050070456535689)
    ·
      refine ⟨9707892069787552842401767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12943856093050070456535689 9707892069787552842401767)
      ·
        refine ⟨14561838104681329263602651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9707892069787552842401767 14561838104681329263602651)
        ·
          refine ⟨21842757157021993895403977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14561838104681329263602651 21842757157021993895403977)
          ·
            refine ⟨16382067867766495421552983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21842757157021993895403977 16382067867766495421552983)
            ·
              refine ⟨24573101801649743132329475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16382067867766495421552983 24573101801649743132329475)
              ·
                refine ⟨36859652702474614698494213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24573101801649743132329475 36859652702474614698494213)
                ·
                  refine ⟨6911184881713990255967665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36859652702474614698494213 6911184881713990255967665)
                  ·
                    refine ⟨5183388661285492691975749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6911184881713990255967665 5183388661285492691975749)
                    ·
                      refine ⟨971885373991029879745453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5183388661285492691975749 971885373991029879745453)
                      ·
                        rfl

theorem cell23_1892740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1892740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892740 prefixEnd_1892740 := by exact prefixLift 1892740
  have htrace : WordTrace (prefixWord ++ tailWord_1892740) baseStart_1892740 baseEnd_1892740 := by
    simpa [prefixWord, tailWord_1892740, baseEnd_1892740] using wordTrace_append hprefix tailTrace_1892740
  have hstable : (prefixWord ++ tailWord_1892740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892740).length < 2 ^ (prefixWord ++ tailWord_1892740).sum := by decide
  have hdescent : baseEnd_1892740 < baseStart_1892740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892744 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1892744 : Nat := 118140960795 + 1892744 * 2 ^ 59
def prefixEnd_1892744 : Nat := 4983230072969 + 3 ^ 40 * 1892744 * 2
def baseEnd_1892744 : Nat := 971887427913647864095435

theorem tailTrace_1892744 : CollatzResearch.WordTrace tailWord_1892744 prefixEnd_1892744 971887427913647864095435 := by
  unfold tailWord_1892744
  simp only [CollatzResearch.WordTrace]
  refine ⟨34517022527459608892334643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46022696703279478523112857 34517022527459608892334643)
  ·
    refine ⟨51775533791189413338501965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34517022527459608892334643 51775533791189413338501965)
    ·
      refine ⟨19415825171696030001938237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51775533791189413338501965 19415825171696030001938237)
      ·
        refine ⟨7280934439386011250726839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19415825171696030001938237 7280934439386011250726839)
        ·
          refine ⟨10921401659079016876090259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7280934439386011250726839 10921401659079016876090259)
          ·
            refine ⟨16382102488618525314135389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10921401659079016876090259 16382102488618525314135389)
            ·
              refine ⟨6143288433231946992800771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16382102488618525314135389 6143288433231946992800771)
              ·
                refine ⟨9214932649847920489201157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6143288433231946992800771 9214932649847920489201157)
                ·
                  refine ⟨1727799871846485091725217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9214932649847920489201157 1727799871846485091725217)
                  ·
                    refine ⟨1295849903884863818793913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727799871846485091725217 1295849903884863818793913)
                    ·
                      refine ⟨971887427913647864095435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295849903884863818793913 971887427913647864095435)
                      ·
                        rfl

theorem cell23_1892744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1892744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892744 prefixEnd_1892744 := by exact prefixLift 1892744
  have htrace : WordTrace (prefixWord ++ tailWord_1892744) baseStart_1892744 baseEnd_1892744 := by
    simpa [prefixWord, tailWord_1892744, baseEnd_1892744] using wordTrace_append hprefix tailTrace_1892744
  have hstable : (prefixWord ++ tailWord_1892744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892744).length < 2 ^ (prefixWord ++ tailWord_1892744).sum := by decide
  have hdescent : baseEnd_1892744 < baseStart_1892744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892753 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_1892753 : Nat := 118140960795 + 1892753 * 2 ^ 59
def prefixEnd_1892753 : Nat := 4983230072969 + 3 ^ 40 * 1892753 * 2
def baseEnd_1892753 : Nat := 971892049239538328882893

theorem tailTrace_1892753 : CollatzResearch.WordTrace tailWord_1892753 prefixEnd_1892753 971892049239538328882893 := by
  unfold tailWord_1892753
  simp only [CollatzResearch.WordTrace]
  refine ⟨69034373311886612321746913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46022915541257741547831275 69034373311886612321746913)
  ·
    refine ⟨51775779983914959241310185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69034373311886612321746913 51775779983914959241310185)
    ·
      refine ⟨38831834987936219430982639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51775779983914959241310185 38831834987936219430982639)
      ·
        refine ⟨58247752481904329146473959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38831834987936219430982639 58247752481904329146473959)
        ·
          refine ⟨87371628722856493719710939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58247752481904329146473959 87371628722856493719710939)
          ·
            refine ⟨131057443084284740579566409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87371628722856493719710939 131057443084284740579566409)
            ·
              refine ⟨98293082313213555434674807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131057443084284740579566409 98293082313213555434674807)
              ·
                refine ⟨147439623469820333152012211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98293082313213555434674807 147439623469820333152012211)
                ·
                  refine ⟨221159435204730499728018317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147439623469820333152012211 221159435204730499728018317)
                  ·
                    refine ⟨82934788201773937398006869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221159435204730499728018317 82934788201773937398006869)
                    ·
                      refine ⟨971892049239538328882893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 82934788201773937398006869 971892049239538328882893)
                      ·
                        rfl

theorem cell23_1892753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_1892753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892753 prefixEnd_1892753 := by exact prefixLift 1892753
  have htrace : WordTrace (prefixWord ++ tailWord_1892753) baseStart_1892753 baseEnd_1892753 := by
    simpa [prefixWord, tailWord_1892753, baseEnd_1892753] using wordTrace_append hprefix tailTrace_1892753
  have hstable : (prefixWord ++ tailWord_1892753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892753).length < 2 ^ (prefixWord ++ tailWord_1892753).sum := by decide
  have hdescent : baseEnd_1892753 < baseStart_1892753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892761 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 2, 2, 2]
def baseStart_1892761 : Nat := 118140960795 + 1892761 * 2 ^ 59
def prefixEnd_1892761 : Nat := 4983230072969 + 3 ^ 40 * 1892761 * 2
def baseEnd_1892761 : Nat := 971896157084774297582857

theorem tailTrace_1892761 : CollatzResearch.WordTrace tailWord_1892761 prefixEnd_1892761 971896157084774297582857 := by
  unfold tailWord_1892761
  simp only [CollatzResearch.WordTrace]
  refine ⟨69034665095857629688038137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46023110063905086458692091 69034665095857629688038137)
  ·
    refine ⟨51775998821893222266028603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69034665095857629688038137 51775998821893222266028603)
    ·
      refine ⟨77663998232839833399042905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51775998821893222266028603 77663998232839833399042905)
      ·
        refine ⟨58247998674629875049282179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77663998232839833399042905 58247998674629875049282179)
        ·
          refine ⟨87371998011944812573923269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58247998674629875049282179 87371998011944812573923269)
          ·
            refine ⟨16382249627239652357610613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87371998011944812573923269 16382249627239652357610613)
            ·
              refine ⟨1535835902553717408525995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16382249627239652357610613 1535835902553717408525995)
              ·
                refine ⟨2303753853830576112788993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1535835902553717408525995 2303753853830576112788993)
                ·
                  refine ⟨1727815390372932084591745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2303753853830576112788993 1727815390372932084591745)
                  ·
                    refine ⟨1295861542779699063443809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1727815390372932084591745 1295861542779699063443809)
                    ·
                      refine ⟨971896157084774297582857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295861542779699063443809 971896157084774297582857)
                      ·
                        rfl

theorem cell23_1892761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_1892761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892761 prefixEnd_1892761 := by exact prefixLift 1892761
  have htrace : WordTrace (prefixWord ++ tailWord_1892761) baseStart_1892761 baseEnd_1892761 := by
    simpa [prefixWord, tailWord_1892761, baseEnd_1892761] using wordTrace_append hprefix tailTrace_1892761
  have hstable : (prefixWord ++ tailWord_1892761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892761).length < 2 ^ (prefixWord ++ tailWord_1892761).sum := by decide
  have hdescent : baseEnd_1892761 < baseStart_1892761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892780 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 2, 5]
def baseStart_1892780 : Nat := 118140960795 + 1892780 * 2 ^ 59
def prefixEnd_1892780 : Nat := 4983230072969 + 3 ^ 40 * 1892780 * 2
def baseEnd_1892780 : Nat := 323968637739069907748423

theorem tailTrace_1892780 : CollatzResearch.WordTrace tailWord_1892780 prefixEnd_1892780 323968637739069907748423 := by
  unfold tailWord_1892780
  simp only [CollatzResearch.WordTrace]
  refine ⟨34517679041394397966489897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46023572055192530621986529 34517679041394397966489897)
  ·
    refine ⟨25888259281045798474867423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34517679041394397966489897 25888259281045798474867423)
    ·
      refine ⟨38832388921568697712301135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25888259281045798474867423 38832388921568697712301135)
      ·
        refine ⟨58248583382353046568451703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38832388921568697712301135 58248583382353046568451703)
        ·
          refine ⟨87372875073529569852677555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58248583382353046568451703 87372875073529569852677555)
          ·
            refine ⟨131059312610294354779016333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87372875073529569852677555 131059312610294354779016333)
            ·
              refine ⟨49147242228860383042131125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131059312610294354779016333 49147242228860383042131125)
              ·
                refine ⟨4607553958955660910199793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49147242228860383042131125 4607553958955660910199793)
                ·
                  refine ⟨3455665469216745682649845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607553958955660910199793 3455665469216745682649845)
                  ·
                    refine ⟨323968637739069907748423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3455665469216745682649845 323968637739069907748423)
                    ·
                      rfl

theorem cell23_1892780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 5].length) (baseStart_1892780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892780 prefixEnd_1892780 := by exact prefixLift 1892780
  have htrace : WordTrace (prefixWord ++ tailWord_1892780) baseStart_1892780 baseEnd_1892780 := by
    simpa [prefixWord, tailWord_1892780, baseEnd_1892780] using wordTrace_append hprefix tailTrace_1892780
  have hstable : (prefixWord ++ tailWord_1892780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892780).length < 2 ^ (prefixWord ++ tailWord_1892780).sum := by decide
  have hdescent : baseEnd_1892780 < baseStart_1892780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892797 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1892797 : Nat := 118140960795 + 1892797 * 2 ^ 59
def prefixEnd_1892797 : Nat := 4983230072969 + 3 ^ 40 * 1892797 * 2
def baseEnd_1892797 : Nat := 323971547462778718910897

theorem tailTrace_1892797 : CollatzResearch.WordTrace tailWord_1892797 prefixEnd_1892797 323971547462778718910897 := by
  unfold tailWord_1892797
  simp only [CollatzResearch.WordTrace]
  refine ⟨69035978123727207836348645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46023985415818138557565763 69035978123727207836348645)
  ·
    refine ⟨12944245898198851469315371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69035978123727207836348645 12944245898198851469315371)
    ·
      refine ⟨19416368847298277203973057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12944245898198851469315371 19416368847298277203973057)
      ·
        refine ⟨14562276635473707902979793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19416368847298277203973057 14562276635473707902979793)
        ·
          refine ⟨10921707476605280927234845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14562276635473707902979793 10921707476605280927234845)
          ·
            refine ⟨4095640303726980347713067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10921707476605280927234845 4095640303726980347713067)
            ·
              refine ⟨6143460455590470521569601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4095640303726980347713067 6143460455590470521569601)
              ·
                refine ⟨4607595341692852891177201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6143460455590470521569601 4607595341692852891177201)
                ·
                  refine ⟨3455696506269639668382901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607595341692852891177201 3455696506269639668382901)
                  ·
                    refine ⟨323971547462778718910897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3455696506269639668382901 323971547462778718910897)
                    ·
                      rfl

theorem cell23_1892797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1892797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892797 prefixEnd_1892797 := by exact prefixLift 1892797
  have htrace : WordTrace (prefixWord ++ tailWord_1892797) baseStart_1892797 baseEnd_1892797 := by
    simpa [prefixWord, tailWord_1892797, baseEnd_1892797] using wordTrace_append hprefix tailTrace_1892797
  have hstable : (prefixWord ++ tailWord_1892797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892797).length < 2 ^ (prefixWord ++ tailWord_1892797).sum := by decide
  have hdescent : baseEnd_1892797 < baseStart_1892797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892817 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 2, 4, 2]
def baseStart_1892817 : Nat := 118140960795 + 1892817 * 2 ^ 59
def prefixEnd_1892817 : Nat := 4983230072969 + 3 ^ 40 * 1892817 * 2
def baseEnd_1892817 : Nat := 971924912001426078482599

theorem tailTrace_1892817 : CollatzResearch.WordTrace tailWord_1892817 prefixEnd_1892817 971924912001426078482599 := by
  unfold tailWord_1892817
  simp only [CollatzResearch.WordTrace]
  refine ⟨69036707583654751252076705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46024471722436500834717803 69036707583654751252076705)
  ·
    refine ⟨51777530687741063439057529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69036707583654751252076705 51777530687741063439057529)
    ·
      refine ⟨38833148015805797579293147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51777530687741063439057529 38833148015805797579293147)
      ·
        refine ⟨58249722023708696368939721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38833148015805797579293147 58249722023708696368939721)
        ·
          refine ⟨43687291517781522276704791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58249722023708696368939721 43687291517781522276704791)
          ·
            refine ⟨65530937276672283415057187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43687291517781522276704791 65530937276672283415057187)
            ·
              refine ⟨98296405915008425122585781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65530937276672283415057187 98296405915008425122585781)
              ·
                refine ⟨9215288054532039855242417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98296405915008425122585781 9215288054532039855242417)
                ·
                  refine ⟨6911466040899029891431813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9215288054532039855242417 6911466040899029891431813)
                  ·
                    refine ⟨1295899882668568104643465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6911466040899029891431813 1295899882668568104643465)
                    ·
                      refine ⟨971924912001426078482599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295899882668568104643465 971924912001426078482599)
                      ·
                        rfl

theorem cell23_1892817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_1892817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892817 prefixEnd_1892817 := by exact prefixLift 1892817
  have htrace : WordTrace (prefixWord ++ tailWord_1892817) baseStart_1892817 baseEnd_1892817 := by
    simpa [prefixWord, tailWord_1892817, baseEnd_1892817] using wordTrace_append hprefix tailTrace_1892817
  have hstable : (prefixWord ++ tailWord_1892817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892817).length < 2 ^ (prefixWord ++ tailWord_1892817).sum := by decide
  have hdescent : baseEnd_1892817 < baseStart_1892817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892844 : List Nat := [2, 2, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_1892844 : Nat := 118140960795 + 1892844 * 2 ^ 59
def prefixEnd_1892844 : Nat := 4983230072969 + 3 ^ 40 * 1892844 * 2
def baseEnd_1892844 : Nat := 323979591993032490948325

theorem tailTrace_1892844 : CollatzResearch.WordTrace tailWord_1892844 prefixEnd_1892844 323979591993032490948325 := by
  unfold tailWord_1892844
  simp only [CollatzResearch.WordTrace]
  refine ⟨34518846177278467431654793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46025128236371289908873057 34518846177278467431654793)
  ·
    refine ⟨25889134632958850573741095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34518846177278467431654793 25889134632958850573741095)
    ·
      refine ⟨38833701949438275860611643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25889134632958850573741095 38833701949438275860611643)
      ·
        refine ⟨58250552924157413790917465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38833701949438275860611643 58250552924157413790917465)
        ·
          refine ⟨43687914693118060343188099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58250552924157413790917465 43687914693118060343188099)
          ·
            refine ⟨65531872039677090514782149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43687914693118060343188099 65531872039677090514782149)
            ·
              refine ⟨12287226007439454471521653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65531872039677090514782149 12287226007439454471521653)
              ·
                refine ⟨1151927438197448856705155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12287226007439454471521653 1151927438197448856705155)
                ·
                  refine ⟨1727891157296173285057733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151927438197448856705155 1727891157296173285057733)
                  ·
                    refine ⟨323979591993032490948325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1727891157296173285057733 323979591993032490948325)
                    ·
                      rfl

theorem cell23_1892844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_1892844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892844 prefixEnd_1892844 := by exact prefixLift 1892844
  have htrace : WordTrace (prefixWord ++ tailWord_1892844) baseStart_1892844 baseEnd_1892844 := by
    simpa [prefixWord, tailWord_1892844, baseEnd_1892844] using wordTrace_append hprefix tailTrace_1892844
  have hstable : (prefixWord ++ tailWord_1892844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892844).length < 2 ^ (prefixWord ++ tailWord_1892844).sum := by decide
  have hdescent : baseEnd_1892844 < baseStart_1892844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892854 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1892854 : Nat := 118140960795 + 1892854 * 2 ^ 59
def prefixEnd_1892854 : Nat := 4983230072969 + 3 ^ 40 * 1892854 * 2
def baseEnd_1892854 : Nat := 971943910785642433719929

theorem tailTrace_1892854 : CollatzResearch.WordTrace tailWord_1892854 prefixEnd_1892854 971943910785642433719929 := by
  unfold tailWord_1892854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4314878567782544160698351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46025371389680471047449077 4314878567782544160698351)
  ·
    refine ⟨6472317851673816241047527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4314878567782544160698351 6472317851673816241047527)
    ·
      refine ⟨9708476777510724361571291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6472317851673816241047527 9708476777510724361571291)
      ·
        refine ⟨14562715166266086542356937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9708476777510724361571291 14562715166266086542356937)
        ·
          refine ⟨10922036374699564906767703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14562715166266086542356937 10922036374699564906767703)
          ·
            refine ⟨16383054562049347360151555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10922036374699564906767703 16383054562049347360151555)
            ·
              refine ⟨24574581843074021040227333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16383054562049347360151555 24574581843074021040227333)
              ·
                refine ⟨4607734095576378945042625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24574581843074021040227333 4607734095576378945042625)
                ·
                  refine ⟨3455800571682284208781969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4607734095576378945042625 3455800571682284208781969)
                  ·
                    refine ⟨2591850428761713156586477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3455800571682284208781969 2591850428761713156586477)
                    ·
                      refine ⟨971943910785642433719929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591850428761713156586477 971943910785642433719929)
                      ·
                        rfl

theorem cell23_1892854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1892854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892854 prefixEnd_1892854 := by exact prefixLift 1892854
  have htrace : WordTrace (prefixWord ++ tailWord_1892854) baseStart_1892854 baseEnd_1892854 := by
    simpa [prefixWord, tailWord_1892854, baseEnd_1892854] using wordTrace_append hprefix tailTrace_1892854
  have hstable : (prefixWord ++ tailWord_1892854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892854).length < 2 ^ (prefixWord ++ tailWord_1892854).sum := by decide
  have hdescent : baseEnd_1892854 < baseStart_1892854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892860 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 2, 6]
def baseStart_1892860 : Nat := 118140960795 + 1892860 * 2 ^ 59
def prefixEnd_1892860 : Nat := 4983230072969 + 3 ^ 40 * 1892860 * 2
def baseEnd_1892860 : Nat := 971946991669569410244901

theorem tailTrace_1892860 : CollatzResearch.WordTrace tailWord_1892860 prefixEnd_1892860 971946991669569410244901 := by
  unfold tailWord_1892860
  simp only [CollatzResearch.WordTrace]
  refine ⟨34519137961249484797946017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46025517281665979730594689 34519137961249484797946017)
  ·
    refine ⟨25889353470937113598459513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34519137961249484797946017 25889353470937113598459513)
    ·
      refine ⟨19417015103202835198844635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25889353470937113598459513 19417015103202835198844635)
      ·
        refine ⟨29125522654804252798266953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19417015103202835198844635 29125522654804252798266953)
        ·
          refine ⟨21844141991103189598700215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29125522654804252798266953 21844141991103189598700215)
          ·
            refine ⟨32766212986654784398050323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21844141991103189598700215 32766212986654784398050323)
            ·
              refine ⟨49149319479982176597075485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32766212986654784398050323 49149319479982176597075485)
              ·
                refine ⟨18430994804993316223903307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49149319479982176597075485 18430994804993316223903307)
                ·
                  refine ⟨27646492207489974335854961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18430994804993316223903307 27646492207489974335854961)
                  ·
                    refine ⟨20734869155617480751891221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27646492207489974335854961 20734869155617480751891221)
                    ·
                      refine ⟨971946991669569410244901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20734869155617480751891221 971946991669569410244901)
                      ·
                        rfl

theorem cell23_1892860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_1892860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892860 prefixEnd_1892860 := by exact prefixLift 1892860
  have htrace : WordTrace (prefixWord ++ tailWord_1892860) baseStart_1892860 baseEnd_1892860 := by
    simpa [prefixWord, tailWord_1892860, baseEnd_1892860] using wordTrace_append hprefix tailTrace_1892860
  have hstable : (prefixWord ++ tailWord_1892860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892860).length < 2 ^ (prefixWord ++ tailWord_1892860).sum := by decide
  have hdescent : baseEnd_1892860 < baseStart_1892860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892901 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 1, 1, 3]
def baseStart_1892901 : Nat := 118140960795 + 1892901 * 2 ^ 59
def prefixEnd_1892901 : Nat := 4983230072969 + 3 ^ 40 * 1892901 * 2
def baseEnd_1892901 : Nat := 971968044376403749832213

theorem tailTrace_1892901 : CollatzResearch.WordTrace tailWord_1892901 prefixEnd_1892901 971968044376403749832213 := by
  unfold tailWord_1892901
  simp only [CollatzResearch.WordTrace]
  refine ⟨69039771315350433598134557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46026514210233622398756371 69039771315350433598134557)
  ·
    refine ⟨25889914243256412599300459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69039771315350433598134557 25889914243256412599300459)
    ·
      refine ⟨38834871364884618898950689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25889914243256412599300459 38834871364884618898950689)
      ·
        refine ⟨29126153523663464174213017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38834871364884618898950689 29126153523663464174213017)
        ·
          refine ⟨21844615142747598130659763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29126153523663464174213017 21844615142747598130659763)
          ·
            refine ⟨32766922714121397195989645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21844615142747598130659763 32766922714121397195989645)
            ·
              refine ⟨12287596017795523948496117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32766922714121397195989645 12287596017795523948496117)
              ·
                refine ⟨1151962126668330370171511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12287596017795523948496117 1151962126668330370171511)
                ·
                  refine ⟨1727943190002495555257267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1151962126668330370171511 1727943190002495555257267)
                  ·
                    refine ⟨2591914785003743332885901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1727943190002495555257267 2591914785003743332885901)
                    ·
                      refine ⟨971968044376403749832213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591914785003743332885901 971968044376403749832213)
                      ·
                        rfl

theorem cell23_1892901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 1, 1, 3].length) (baseStart_1892901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892901 prefixEnd_1892901 := by exact prefixLift 1892901
  have htrace : WordTrace (prefixWord ++ tailWord_1892901) baseStart_1892901 baseEnd_1892901 := by
    simpa [prefixWord, tailWord_1892901, baseEnd_1892901] using wordTrace_append hprefix tailTrace_1892901
  have hstable : (prefixWord ++ tailWord_1892901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892901).length < 2 ^ (prefixWord ++ tailWord_1892901).sum := by decide
  have hdescent : baseEnd_1892901 < baseStart_1892901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892907 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 1, 8, 2]
def baseStart_1892907 : Nat := 118140960795 + 1892907 * 2 ^ 59
def prefixEnd_1892907 : Nat := 4983230072969 + 3 ^ 40 * 1892907 * 2
def baseEnd_1892907 : Nat := 971971125260330726357185

theorem tailTrace_1892907 : CollatzResearch.WordTrace tailWord_1892907 prefixEnd_1892907 971971125260330726357185 := by
  unfold tailWord_1892907
  simp only [CollatzResearch.WordTrace]
  refine ⟨69039990153328696622852975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46026660102219131081901983 69039990153328696622852975)
  ·
    refine ⟨103559985229993044934279463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69039990153328696622852975 103559985229993044934279463)
    ·
      refine ⟨155339977844989567401419195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103559985229993044934279463 155339977844989567401419195)
      ·
        refine ⟨233009966767484351102128793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155339977844989567401419195 233009966767484351102128793)
        ·
          refine ⟨174757475075613263326596595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233009966767484351102128793 174757475075613263326596595)
          ·
            refine ⟨262136212613419894989894893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174757475075613263326596595 262136212613419894989894893)
            ·
              refine ⟨98301079730032460621210585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 262136212613419894989894893 98301079730032460621210585)
              ·
                refine ⟨73725809797524345465907939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98301079730032460621210585 73725809797524345465907939)
                ·
                  refine ⟨110588714696286518198861909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73725809797524345465907939 110588714696286518198861909)
                  ·
                    refine ⟨1295961500347107635142913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110588714696286518198861909 1295961500347107635142913)
                    ·
                      refine ⟨971971125260330726357185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1295961500347107635142913 971971125260330726357185)
                      ·
                        rfl

theorem cell23_1892907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8, 2].length) (baseStart_1892907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892907 prefixEnd_1892907 := by exact prefixLift 1892907
  have htrace : WordTrace (prefixWord ++ tailWord_1892907) baseStart_1892907 baseEnd_1892907 := by
    simpa [prefixWord, tailWord_1892907, baseEnd_1892907] using wordTrace_append hprefix tailTrace_1892907
  have hstable : (prefixWord ++ tailWord_1892907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892907).length < 2 ^ (prefixWord ++ tailWord_1892907).sum := by decide
  have hdescent : baseEnd_1892907 < baseStart_1892907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892918 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_1892918 : Nat := 118140960795 + 1892918 * 2 ^ 59
def prefixEnd_1892918 : Nat := 4983230072969 + 3 ^ 40 * 1892918 * 2
def baseEnd_1892918 : Nat := 971976773547530183319635

theorem tailTrace_1892918 : CollatzResearch.WordTrace tailWord_1892918 prefixEnd_1892918 971976773547530183319635 := by
  unfold tailWord_1892918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315024459768052843843963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46026927570859230334335605 4315024459768052843843963)
  ·
    refine ⟨6472536689652079265765945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315024459768052843843963 6472536689652079265765945)
    ·
      refine ⟨4854402517239059449324459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6472536689652079265765945 4854402517239059449324459)
      ·
        refine ⟨7281603775858589173986689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854402517239059449324459 7281603775858589173986689)
        ·
          refine ⟨5461202831893941880490017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281603775858589173986689 5461202831893941880490017)
          ·
            refine ⟨4095902123920456410367513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5461202831893941880490017 4095902123920456410367513)
            ·
              refine ⟨3071926592940342307775635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4095902123920456410367513 3071926592940342307775635)
              ·
                refine ⟨4607889889410513461663453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3071926592940342307775635 4607889889410513461663453)
                ·
                  refine ⟨1727958708528942548123795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4607889889410513461663453 1727958708528942548123795)
                  ·
                    refine ⟨2591938062793413822185693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1727958708528942548123795 2591938062793413822185693)
                    ·
                      refine ⟨971976773547530183319635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2591938062793413822185693 971976773547530183319635)
                      ·
                        rfl

theorem cell23_1892918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_1892918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892918 prefixEnd_1892918 := by exact prefixLift 1892918
  have htrace : WordTrace (prefixWord ++ tailWord_1892918) baseStart_1892918 baseEnd_1892918 := by
    simpa [prefixWord, tailWord_1892918, baseEnd_1892918] using wordTrace_append hprefix tailTrace_1892918
  have hstable : (prefixWord ++ tailWord_1892918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892918).length < 2 ^ (prefixWord ++ tailWord_1892918).sum := by decide
  have hdescent : baseEnd_1892918 < baseStart_1892918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892927 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 5]
def baseStart_1892927 : Nat := 118140960795 + 1892927 * 2 ^ 59
def prefixEnd_1892927 : Nat := 4983230072969 + 3 ^ 40 * 1892927 * 2
def baseEnd_1892927 : Nat := 971981394873420648107093

theorem tailTrace_1892927 : CollatzResearch.WordTrace tailWord_1892927 prefixEnd_1892927 971981394873420648107093 := by
  unfold tailWord_1892927
  simp only [CollatzResearch.WordTrace]
  refine ⟨69040719613256240038581035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46027146408837493359054023 69040719613256240038581035)
  ·
    refine ⟨103561079419884360057871553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69040719613256240038581035 103561079419884360057871553)
    ·
      refine ⟨77670809564913270043403665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103561079419884360057871553 77670809564913270043403665)
      ·
        refine ⟨58253107173684952532552749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77670809564913270043403665 58253107173684952532552749)
        ·
          refine ⟨21844915190131857199707281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58253107173684952532552749 21844915190131857199707281)
          ·
            refine ⟨16383686392598892899780461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21844915190131857199707281 16383686392598892899780461)
            ·
              refine ⟨6143882397224584837417673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16383686392598892899780461 6143882397224584837417673)
              ·
                refine ⟨4607911797918438628063255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6143882397224584837417673 4607911797918438628063255)
                ·
                  refine ⟨6911867696877657942094883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4607911797918438628063255 6911867696877657942094883)
                  ·
                    refine ⟨10367801545316486913142325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6911867696877657942094883 10367801545316486913142325)
                    ·
                      refine ⟨971981394873420648107093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10367801545316486913142325 971981394873420648107093)
                      ·
                        rfl

theorem cell23_1892927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 5].length) (baseStart_1892927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892927 prefixEnd_1892927 := by exact prefixLift 1892927
  have htrace : WordTrace (prefixWord ++ tailWord_1892927) baseStart_1892927 baseEnd_1892927 := by
    simpa [prefixWord, tailWord_1892927, baseEnd_1892927] using wordTrace_append hprefix tailTrace_1892927
  have hstable : (prefixWord ++ tailWord_1892927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892927).length < 2 ^ (prefixWord ++ tailWord_1892927).sum := by decide
  have hdescent : baseEnd_1892927 < baseStart_1892927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892941 : List Nat := [1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1892941 : Nat := 118140960795 + 1892941 * 2 ^ 59
def prefixEnd_1892941 : Nat := 4983230072969 + 3 ^ 40 * 1892941 * 2
def baseEnd_1892941 : Nat := 971988583602583593332029

theorem tailTrace_1892941 : CollatzResearch.WordTrace tailWord_1892941 prefixEnd_1892941 971988583602583593332029 := by
  unfold tailWord_1892941
  simp only [CollatzResearch.WordTrace]
  refine ⟨69041230235205520429590677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46027486823470346953060451 69041230235205520429590677)
  ·
    refine ⟨3236307667275258770137063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69041230235205520429590677 3236307667275258770137063)
    ·
      refine ⟨4854461500912888155205595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3236307667275258770137063 4854461500912888155205595)
      ·
        refine ⟨7281692251369332232808393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4854461500912888155205595 7281692251369332232808393)
        ·
          refine ⟨5461269188526999174606295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7281692251369332232808393 5461269188526999174606295)
          ·
            refine ⟨8191903782790498761909443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5461269188526999174606295 8191903782790498761909443)
            ·
              refine ⟨12287855674185748142864165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8191903782790498761909443 12287855674185748142864165)
              ·
                refine ⟨2303972938909827776787031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12287855674185748142864165 2303972938909827776787031)
                ·
                  refine ⟨3455959408364741665180547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2303972938909827776787031 3455959408364741665180547)
                  ·
                    refine ⟨5183939112547112497770821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3455959408364741665180547 5183939112547112497770821)
                    ·
                      refine ⟨971988583602583593332029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5183939112547112497770821 971988583602583593332029)
                      ·
                        rfl

theorem cell23_1892941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1892941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892941 prefixEnd_1892941 := by exact prefixLift 1892941
  have htrace : WordTrace (prefixWord ++ tailWord_1892941) baseStart_1892941 baseEnd_1892941 := by
    simpa [prefixWord, tailWord_1892941, baseEnd_1892941] using wordTrace_append hprefix tailTrace_1892941
  have hstable : (prefixWord ++ tailWord_1892941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892941).length < 2 ^ (prefixWord ++ tailWord_1892941).sum := by decide
  have hdescent : baseEnd_1892941 < baseStart_1892941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1892984 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 5, 3, 2]
def baseStart_1892984 : Nat := 118140960795 + 1892984 * 2 ^ 59
def prefixEnd_1892984 : Nat := 4983230072969 + 3 ^ 40 * 1892984 * 2
def baseEnd_1892984 : Nat := 972010663270726925094331

theorem tailTrace_1892984 : CollatzResearch.WordTrace tailWord_1892984 prefixEnd_1892984 972010663270726925094331 := by
  unfold tailWord_1892984
  simp only [CollatzResearch.WordTrace]
  refine ⟨34521399287024869386703003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46028532382699825848937337 34521399287024869386703003)
  ·
    refine ⟨51782098930537304080054505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34521399287024869386703003 51782098930537304080054505)
    ·
      refine ⟨38836574197902978060040879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51782098930537304080054505 38836574197902978060040879)
      ·
        refine ⟨58254861296854467090061319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38836574197902978060040879 58254861296854467090061319)
        ·
          refine ⟨87382291945281700635091979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58254861296854467090061319 87382291945281700635091979)
          ·
            refine ⟨131073437917922550952637969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87382291945281700635091979 131073437917922550952637969)
            ·
              refine ⟨98305078438441913214478477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131073437917922550952637969 98305078438441913214478477)
              ·
                refine ⟨36864404414415717455429429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98305078438441913214478477 36864404414415717455429429)
                ·
                  refine ⟨3456037913851473511446509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36864404414415717455429429 3456037913851473511446509)
                  ·
                    refine ⟨1296014217694302566792441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456037913851473511446509 1296014217694302566792441)
                    ·
                      refine ⟨972010663270726925094331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296014217694302566792441 972010663270726925094331)
                      ·
                        rfl

theorem cell23_1892984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5, 3, 2].length) (baseStart_1892984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1892984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1892984 prefixEnd_1892984 := by exact prefixLift 1892984
  have htrace : WordTrace (prefixWord ++ tailWord_1892984) baseStart_1892984 baseEnd_1892984 := by
    simpa [prefixWord, tailWord_1892984, baseEnd_1892984] using wordTrace_append hprefix tailTrace_1892984
  have hstable : (prefixWord ++ tailWord_1892984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1892984).length < 2 ^ (prefixWord ++ tailWord_1892984).sum := by decide
  have hdescent : baseEnd_1892984 < baseStart_1892984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1892984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893017 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 5]
def baseStart_1893017 : Nat := 118140960795 + 1893017 * 2 ^ 59
def prefixEnd_1893017 : Nat := 4983230072969 + 3 ^ 40 * 1893017 * 2
def baseEnd_1893017 : Nat := 972027608132325295981679

theorem tailTrace_1893017 : CollatzResearch.WordTrace tailWord_1893017 prefixEnd_1893017 972027608132325295981679 := by
  unfold tailWord_1893017
  simp only [CollatzResearch.WordTrace]
  refine ⟨69044002182930185409357305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46029334788620123606238203 69044002182930185409357305)
  ·
    refine ⟨51783001637197639057017979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69044002182930185409357305 51783001637197639057017979)
    ·
      refine ⟨77674502455796458585526969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51783001637197639057017979 77674502455796458585526969)
      ·
        refine ⟨58255876841847343939145227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77674502455796458585526969 58255876841847343939145227)
        ·
          refine ⟨87383815262771015908717841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58255876841847343939145227 87383815262771015908717841)
          ·
            refine ⟨65537861447078261931538381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87383815262771015908717841 65537861447078261931538381)
            ·
              refine ⟨24576698042654348224326893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65537861447078261931538381 24576698042654348224326893)
              ·
                refine ⟨9216261765995380584122585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24576698042654348224326893 9216261765995380584122585)
                ·
                  refine ⟨6912196324496535438091939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216261765995380584122585 6912196324496535438091939)
                  ·
                    refine ⟨10368294486744803157137909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6912196324496535438091939 10368294486744803157137909)
                    ·
                      refine ⟨972027608132325295981679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10368294486744803157137909 972027608132325295981679)
                      ·
                        rfl

theorem cell23_1893017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_1893017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893017 prefixEnd_1893017 := by exact prefixLift 1893017
  have htrace : WordTrace (prefixWord ++ tailWord_1893017) baseStart_1893017 baseEnd_1893017 := by
    simpa [prefixWord, tailWord_1893017, baseEnd_1893017] using wordTrace_append hprefix tailTrace_1893017
  have hstable : (prefixWord ++ tailWord_1893017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893017).length < 2 ^ (prefixWord ++ tailWord_1893017).sum := by decide
  have hdescent : baseEnd_1893017 < baseStart_1893017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893041 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 2, 6]
def baseStart_1893041 : Nat := 118140960795 + 1893041 * 2 ^ 59
def prefixEnd_1893041 : Nat := 4983230072969 + 3 ^ 40 * 1893041 * 2
def baseEnd_1893041 : Nat := 324013310556011067360523

theorem tailTrace_1893041 : CollatzResearch.WordTrace tailWord_1893041 prefixEnd_1893041 324013310556011067360523 := by
  unfold tailWord_1893041
  simp only [CollatzResearch.WordTrace]
  refine ⟨69044877534843237508230977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46029918356562158338820651 69044877534843237508230977)
  ·
    refine ⟨51783658151132428131173233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69044877534843237508230977 51783658151132428131173233)
    ·
      refine ⟨38837743613349321098379925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51783658151132428131173233 38837743613349321098379925)
      ·
        refine ⟨1820519231875749426486559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38837743613349321098379925 1820519231875749426486559)
        ·
          refine ⟨2730778847813624139729839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820519231875749426486559 2730778847813624139729839)
          ·
            refine ⟨4096168271720436209594759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2730778847813624139729839 4096168271720436209594759)
            ·
              refine ⟨6144252407580654314392139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4096168271720436209594759 6144252407580654314392139)
              ·
                refine ⟨9216378611370981471588209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6144252407580654314392139 9216378611370981471588209)
                ·
                  refine ⟨6912283958528236103691157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9216378611370981471588209 6912283958528236103691157)
                  ·
                    refine ⟨324013310556011067360523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6912283958528236103691157 324013310556011067360523)
                    ·
                      rfl

theorem cell23_1893041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_1893041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893041 prefixEnd_1893041 := by exact prefixLift 1893041
  have htrace : WordTrace (prefixWord ++ tailWord_1893041) baseStart_1893041 baseEnd_1893041 := by
    simpa [prefixWord, tailWord_1893041, baseEnd_1893041] using wordTrace_append hprefix tailTrace_1893041
  have hstable : (prefixWord ++ tailWord_1893041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893041).length < 2 ^ (prefixWord ++ tailWord_1893041).sum := by decide
  have hdescent : baseEnd_1893041 < baseStart_1893041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893054 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_1893054 : Nat := 118140960795 + 1893054 * 2 ^ 59
def prefixEnd_1893054 : Nat := 4983230072969 + 3 ^ 40 * 1893054 * 2
def baseEnd_1893054 : Nat := 108005178546282405691001

theorem tailTrace_1893054 : CollatzResearch.WordTrace tailWord_1893054 prefixEnd_1893054 108005178546282405691001 := by
  unfold tailWord_1893054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8630668960474517591056777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46030234455864093818969477 8630668960474517591056777)
  ·
    refine ⟨6473001720355888193292583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8630668960474517591056777 6473001720355888193292583)
    ·
      refine ⟨9709502580533832289938875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473001720355888193292583 9709502580533832289938875)
      ·
        refine ⟨14564253870800748434908313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9709502580533832289938875 14564253870800748434908313)
        ·
          refine ⟨10923190403100561326181235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14564253870800748434908313 10923190403100561326181235)
          ·
            refine ⟨16384785604650841989271853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10923190403100561326181235 16384785604650841989271853)
            ·
              refine ⟨6144294601744065745976945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16384785604650841989271853 6144294601744065745976945)
              ·
                refine ⟨4608220951308049309482709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144294601744065745976945 4608220951308049309482709)
                ·
                  refine ⟨108005178546282405691001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4608220951308049309482709 108005178546282405691001)
                  ·
                    rfl

theorem cell23_1893054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_1893054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893054 prefixEnd_1893054 := by exact prefixLift 1893054
  have htrace : WordTrace (prefixWord ++ tailWord_1893054) baseStart_1893054 baseEnd_1893054 := by
    simpa [prefixWord, tailWord_1893054, baseEnd_1893054] using wordTrace_append hprefix tailTrace_1893054
  have hstable : (prefixWord ++ tailWord_1893054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893054).length < 2 ^ (prefixWord ++ tailWord_1893054).sum := by decide
  have hdescent : baseEnd_1893054 < baseStart_1893054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893069 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1893069 : Nat := 118140960795 + 1893069 * 2 ^ 59
def prefixEnd_1893069 : Nat := 4983230072969 + 3 ^ 40 * 1893069 * 2
def baseEnd_1893069 : Nat := 972054309126359092531441

theorem tailTrace_1893069 : CollatzResearch.WordTrace tailWord_1893069 prefixEnd_1893069 972054309126359092531441 := by
  unfold tailWord_1893069
  simp only [CollatzResearch.WordTrace]
  refine ⟨69045898778741798290250261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46030599185827865526833507 69045898778741798290250261)
  ·
    refine ⟨3236526505253521794855481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69045898778741798290250261 3236526505253521794855481)
    ·
      refine ⟨2427394878940141346141611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236526505253521794855481 2427394878940141346141611)
      ·
        refine ⟨3641092318410212019212417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427394878940141346141611 3641092318410212019212417)
        ·
          refine ⟨2730819238807659014409313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3641092318410212019212417 2730819238807659014409313)
          ·
            refine ⟨2048114429105744260806985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2730819238807659014409313 2048114429105744260806985)
            ·
              refine ⟨1536085821829308195605239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048114429105744260806985 1536085821829308195605239)
              ·
                refine ⟨2304128732743962293407859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1536085821829308195605239 2304128732743962293407859)
                ·
                  refine ⟨3456193099115943440111789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304128732743962293407859 3456193099115943440111789)
                  ·
                    refine ⟨1296072412168478790041921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456193099115943440111789 1296072412168478790041921)
                    ·
                      refine ⟨972054309126359092531441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296072412168478790041921 972054309126359092531441)
                      ·
                        rfl

theorem cell23_1893069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1893069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893069 prefixEnd_1893069 := by exact prefixLift 1893069
  have htrace : WordTrace (prefixWord ++ tailWord_1893069) baseStart_1893069 baseEnd_1893069 := by
    simpa [prefixWord, tailWord_1893069, baseEnd_1893069] using wordTrace_append hprefix tailTrace_1893069
  have hstable : (prefixWord ++ tailWord_1893069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893069).length < 2 ^ (prefixWord ++ tailWord_1893069).sum := by decide
  have hdescent : baseEnd_1893069 < baseStart_1893069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893141 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 3]
def baseStart_1893141 : Nat := 118140960795 + 1893141 * 2 ^ 59
def prefixEnd_1893141 : Nat := 4983230072969 + 3 ^ 40 * 1893141 * 2
def baseEnd_1893141 : Nat := 972091279733482810831109

theorem tailTrace_1893141 : CollatzResearch.WordTrace tailWord_1893141 prefixEnd_1893141 972091279733482810831109 := by
  unfold tailWord_1893141
  simp only [CollatzResearch.WordTrace]
  refine ⟨69048524834480954586871277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46032349889653969724580851 69048524834480954586871277)
  ·
    refine ⟨25893196812930357970076729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69048524834480954586871277 25893196812930357970076729)
    ·
      refine ⟨19419897609697768477557547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25893196812930357970076729 19419897609697768477557547)
      ·
        refine ⟨29129846414546652716336321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19419897609697768477557547 29129846414546652716336321)
        ·
          refine ⟨21847384810909989537252241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29129846414546652716336321 21847384810909989537252241)
          ·
            refine ⟨16385538608182492152939181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21847384810909989537252241 16385538608182492152939181)
            ·
              refine ⟨6144576978068434557352193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16385538608182492152939181 6144576978068434557352193)
              ·
                refine ⟨4608432733551325918014145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144576978068434557352193 4608432733551325918014145)
                ·
                  refine ⟨3456324550163494438510609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4608432733551325918014145 3456324550163494438510609)
                  ·
                    refine ⟨2592243412622620828882957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3456324550163494438510609 2592243412622620828882957)
                    ·
                      refine ⟨972091279733482810831109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2592243412622620828882957 972091279733482810831109)
                      ·
                        rfl

theorem cell23_1893141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_1893141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893141 prefixEnd_1893141 := by exact prefixLift 1893141
  have htrace : WordTrace (prefixWord ++ tailWord_1893141) baseStart_1893141 baseEnd_1893141 := by
    simpa [prefixWord, tailWord_1893141, baseEnd_1893141] using wordTrace_append hprefix tailTrace_1893141
  have hstable : (prefixWord ++ tailWord_1893141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893141).length < 2 ^ (prefixWord ++ tailWord_1893141).sum := by decide
  have hdescent : baseEnd_1893141 < baseStart_1893141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893144 : List Nat := [2, 1, 2, 3, 1, 1, 1, 6, 6]
def baseStart_1893144 : Nat := 118140960795 + 1893144 * 2 ^ 59
def prefixEnd_1893144 : Nat := 4983230072969 + 3 ^ 40 * 1893144 * 2
def baseEnd_1893144 : Nat := 108010313352827366565955

theorem tailTrace_1893144 : CollatzResearch.WordTrace tailWord_1893144 prefixEnd_1893144 108010313352827366565955 := by
  unfold tailWord_1893144
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524317126735043049615243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46032422835646724066153657 34524317126735043049615243)
  ·
    refine ⟨51786475690102564574422865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34524317126735043049615243 51786475690102564574422865)
    ·
      refine ⟨38839856767576923430817149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51786475690102564574422865 38839856767576923430817149)
      ·
        refine ⟨14564946287841346286556431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38839856767576923430817149 14564946287841346286556431)
        ·
          refine ⟨21847419431762019429834647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564946287841346286556431 21847419431762019429834647)
          ·
            refine ⟨32771129147643029144751971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21847419431762019429834647 32771129147643029144751971)
            ·
              refine ⟨49156693721464543717127957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32771129147643029144751971 49156693721464543717127957)
              ·
                refine ⟨2304220018193650486740373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49156693721464543717127957 2304220018193650486740373)
                ·
                  refine ⟨108010313352827366565955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2304220018193650486740373 108010313352827366565955)
                  ·
                    rfl

theorem cell23_1893144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 6].length) (baseStart_1893144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893144 prefixEnd_1893144 := by exact prefixLift 1893144
  have htrace : WordTrace (prefixWord ++ tailWord_1893144) baseStart_1893144 baseEnd_1893144 := by
    simpa [prefixWord, tailWord_1893144, baseEnd_1893144] using wordTrace_append hprefix tailTrace_1893144
  have hstable : (prefixWord ++ tailWord_1893144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893144).length < 2 ^ (prefixWord ++ tailWord_1893144).sum := by decide
  have hdescent : baseEnd_1893144 < baseStart_1893144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893148 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1893148 : Nat := 118140960795 + 1893148 * 2 ^ 59
def prefixEnd_1893148 : Nat := 4983230072969 + 3 ^ 40 * 1893148 * 2
def baseEnd_1893148 : Nat := 324031624699354761147859

theorem tailTrace_1893148 : CollatzResearch.WordTrace tailWord_1893148 prefixEnd_1893148 324031624699354761147859 := by
  unfold tailWord_1893148
  simp only [CollatzResearch.WordTrace]
  refine ⟨34524390072727797391188049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46032520096970396521584065 34524390072727797391188049)
  ·
    refine ⟨25893292554545848043391037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34524390072727797391188049 25893292554545848043391037)
    ·
      refine ⟨9709984707954693016271639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25893292554545848043391037 9709984707954693016271639)
      ·
        refine ⟨14564977061932039524407459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9709984707954693016271639 14564977061932039524407459)
        ·
          refine ⟨21847465592898059286611189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14564977061932039524407459 21847465592898059286611189)
          ·
            refine ⟨2048199899334193058119799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21847465592898059286611189 2048199899334193058119799)
            ·
              refine ⟨3072299849001289587179699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048199899334193058119799 3072299849001289587179699)
              ·
                refine ⟨4608449773501934380769549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072299849001289587179699 4608449773501934380769549)
                ·
                  refine ⟨1728168665063225392788581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4608449773501934380769549 1728168665063225392788581)
                  ·
                    refine ⟨324031624699354761147859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1728168665063225392788581 324031624699354761147859)
                    ·
                      rfl

theorem cell23_1893148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1893148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893148 prefixEnd_1893148 := by exact prefixLift 1893148
  have htrace : WordTrace (prefixWord ++ tailWord_1893148) baseStart_1893148 baseEnd_1893148 := by
    simpa [prefixWord, tailWord_1893148, baseEnd_1893148] using wordTrace_append hprefix tailTrace_1893148
  have hstable : (prefixWord ++ tailWord_1893148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893148).length < 2 ^ (prefixWord ++ tailWord_1893148).sum := by decide
  have hdescent : baseEnd_1893148 < baseStart_1893148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893205 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 1, 1, 3]
def baseStart_1893205 : Nat := 118140960795 + 1893205 * 2 ^ 59
def prefixEnd_1893205 : Nat := 4983230072969 + 3 ^ 40 * 1893205 * 2
def baseEnd_1893205 : Nat := 972124142495370560430815

theorem tailTrace_1893205 : CollatzResearch.WordTrace tailWord_1893205 prefixEnd_1893205 972124142495370560430815 := by
  unfold tailWord_1893205
  simp only [CollatzResearch.WordTrace]
  refine ⟨69050859106249093517201069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46033906070832729011467379 69050859106249093517201069)
  ·
    refine ⟨25894072164843410068950401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69050859106249093517201069 25894072164843410068950401)
    ·
      refine ⟨19420554123632557551712801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25894072164843410068950401 19420554123632557551712801)
      ·
        refine ⟨14565415592724418163784601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19420554123632557551712801 14565415592724418163784601)
        ·
          refine ⟨10924061694543313622838451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14565415592724418163784601 10924061694543313622838451)
          ·
            refine ⟨16386092541814970434257677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10924061694543313622838451 16386092541814970434257677)
            ·
              refine ⟨6144784703180613912846629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16386092541814970434257677 6144784703180613912846629)
              ·
                refine ⟨1152147131846365108658743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6144784703180613912846629 1152147131846365108658743)
                ·
                  refine ⟨1728220697769547662988115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152147131846365108658743 1728220697769547662988115)
                  ·
                    refine ⟨2592331046654321494482173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1728220697769547662988115 2592331046654321494482173)
                    ·
                      refine ⟨972124142495370560430815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2592331046654321494482173 972124142495370560430815)
                      ·
                        rfl

theorem cell23_1893205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_1893205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893205 prefixEnd_1893205 := by exact prefixLift 1893205
  have htrace : WordTrace (prefixWord ++ tailWord_1893205) baseStart_1893205 baseEnd_1893205 := by
    simpa [prefixWord, tailWord_1893205, baseEnd_1893205] using wordTrace_append hprefix tailTrace_1893205
  have hstable : (prefixWord ++ tailWord_1893205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893205).length < 2 ^ (prefixWord ++ tailWord_1893205).sum := by decide
  have hdescent : baseEnd_1893205 < baseStart_1893205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893234 : List Nat := [3, 2, 1, 2, 1, 1, 2, 11]
def baseStart_1893234 : Nat := 118140960795 + 1893234 * 2 ^ 59
def prefixEnd_1893234 : Nat := 4983230072969 + 3 ^ 40 * 1893234 * 2
def baseEnd_1893234 : Nat := 36005149386457442480303

theorem tailTrace_1893234 : CollatzResearch.WordTrace tailWord_1893234 prefixEnd_1893234 36005149386457442480303 := by
  unfold tailWord_1893234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17262979205786007867501689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46034611215429354313337837 17262979205786007867501689)
  ·
    refine ⟨12947234404339505900626267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17262979205786007867501689 12947234404339505900626267)
    ·
      refine ⟨19420851606509258850939401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12947234404339505900626267 19420851606509258850939401)
      ·
        refine ⟨14565638704881944138204551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19420851606509258850939401 14565638704881944138204551)
        ·
          refine ⟨21848458057322916207306827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14565638704881944138204551 21848458057322916207306827)
          ·
            refine ⟨32772687085984374310960241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21848458057322916207306827 32772687085984374310960241)
            ·
              refine ⟨24579515314488280733220181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32772687085984374310960241 24579515314488280733220181)
              ·
                refine ⟨36005149386457442480303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24579515314488280733220181 36005149386457442480303)
                ·
                  rfl

theorem cell23_1893234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_1893234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893234 prefixEnd_1893234 := by exact prefixLift 1893234
  have htrace : WordTrace (prefixWord ++ tailWord_1893234) baseStart_1893234 baseEnd_1893234 := by
    simpa [prefixWord, tailWord_1893234, baseEnd_1893234] using wordTrace_append hprefix tailTrace_1893234
  have hstable : (prefixWord ++ tailWord_1893234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893234).length < 2 ^ (prefixWord ++ tailWord_1893234).sum := by decide
  have hdescent : baseEnd_1893234 < baseStart_1893234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893238 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_1893238 : Nat := 118140960795 + 1893238 * 2 ^ 59
def prefixEnd_1893238 : Nat := 4983230072969 + 3 ^ 40 * 1893238 * 2
def baseEnd_1893238 : Nat := 324047029118989643772721

theorem tailTrace_1893238 : CollatzResearch.WordTrace tailWord_1893238 prefixEnd_1893238 324047029118989643772721 := by
  unfold tailWord_1893238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315753919695596259572023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46034708476753026768768245 4315753919695596259572023)
  ·
    refine ⟨6473630879543394389358035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315753919695596259572023 6473630879543394389358035)
    ·
      refine ⟨9710446319315091584037053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6473630879543394389358035 9710446319315091584037053)
      ·
        refine ⟨3641417369743159344013895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9710446319315091584037053 3641417369743159344013895)
        ·
          refine ⟨5462126054614739016020843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3641417369743159344013895 5462126054614739016020843)
          ·
            refine ⟨8193189081922108524031265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5462126054614739016020843 8193189081922108524031265)
            ·
              refine ⟨6144891811441581393023449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8193189081922108524031265 6144891811441581393023449)
              ·
                refine ⟨4608668858581186044767587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144891811441581393023449 4608668858581186044767587)
                ·
                  refine ⟨6913003287871779067151381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608668858581186044767587 6913003287871779067151381)
                  ·
                    refine ⟨324047029118989643772721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6913003287871779067151381 324047029118989643772721)
                    ·
                      rfl

theorem cell23_1893238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_1893238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893238 prefixEnd_1893238 := by exact prefixLift 1893238
  have htrace : WordTrace (prefixWord ++ tailWord_1893238) baseStart_1893238 baseEnd_1893238 := by
    simpa [prefixWord, tailWord_1893238, baseEnd_1893238] using wordTrace_append hprefix tailTrace_1893238
  have hstable : (prefixWord ++ tailWord_1893238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893238).length < 2 ^ (prefixWord ++ tailWord_1893238).sum := by decide
  have hdescent : baseEnd_1893238 < baseStart_1893238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893241 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 4]
def baseStart_1893241 : Nat := 118140960795 + 1893241 * 2 ^ 59
def prefixEnd_1893241 : Nat := 4983230072969 + 3 ^ 40 * 1893241 * 2
def baseEnd_1893241 : Nat := 972142627798932419580649

theorem tailTrace_1893241 : CollatzResearch.WordTrace tailWord_1893241 prefixEnd_1893241 972142627798932419580649 := by
  unfold tailWord_1893241
  simp only [CollatzResearch.WordTrace]
  refine ⟨69052172134118671665511577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46034781422745781110341051 69052172134118671665511577)
  ·
    refine ⟨51789129100589003749133683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69052172134118671665511577 51789129100589003749133683)
    ·
      refine ⟨77683693650883505623700525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51789129100589003749133683 77683693650883505623700525)
      ·
        refine ⟨29131385119081314608887697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77683693650883505623700525 29131385119081314608887697)
        ·
          refine ⟨21848538839310985956665773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29131385119081314608887697 21848538839310985956665773)
          ·
            refine ⟨8193202064741619733749665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21848538839310985956665773 8193202064741619733749665)
            ·
              refine ⟨6144901548556214800312249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8193202064741619733749665 6144901548556214800312249)
              ·
                refine ⟨4608676161417161100234187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6144901548556214800312249 4608676161417161100234187)
                ·
                  refine ⟨6913014242125741650351281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4608676161417161100234187 6913014242125741650351281)
                  ·
                    refine ⟨5184760681594306237763461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6913014242125741650351281 5184760681594306237763461)
                    ·
                      refine ⟨972142627798932419580649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5184760681594306237763461 972142627798932419580649)
                      ·
                        rfl

theorem cell23_1893241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_1893241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893241 prefixEnd_1893241 := by exact prefixLift 1893241
  have htrace : WordTrace (prefixWord ++ tailWord_1893241) baseStart_1893241 baseEnd_1893241 := by
    simpa [prefixWord, tailWord_1893241, baseEnd_1893241] using wordTrace_append hprefix tailTrace_1893241
  have hstable : (prefixWord ++ tailWord_1893241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893241).length < 2 ^ (prefixWord ++ tailWord_1893241).sum := by decide
  have hdescent : baseEnd_1893241 < baseStart_1893241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893255 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 2, 4]
def baseStart_1893255 : Nat := 118140960795 + 1893255 * 2 ^ 59
def prefixEnd_1893255 : Nat := 4983230072969 + 3 ^ 40 * 1893255 * 2
def baseEnd_1893255 : Nat := 324049938842698454935195

theorem tailTrace_1893255 : CollatzResearch.WordTrace tailWord_1893255 prefixEnd_1893255 324049938842698454935195 := by
  unfold tailWord_1893255
  simp only [CollatzResearch.WordTrace]
  refine ⟨69052682756067952056521219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46035121837378634704347479 69052682756067952056521219)
  ·
    refine ⟨103579024134101928084781829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69052682756067952056521219 103579024134101928084781829)
    ·
      refine ⟨19421067025144111515896593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103579024134101928084781829 19421067025144111515896593)
      ·
        refine ⟨14565800268858083636922445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19421067025144111515896593 14565800268858083636922445)
        ·
          refine ⟨5462175100821781363845917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14565800268858083636922445 5462175100821781363845917)
          ·
            refine ⟨2048315662808168011442219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5462175100821781363845917 2048315662808168011442219)
            ·
              refine ⟨3072473494212252017163329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048315662808168011442219 3072473494212252017163329)
              ·
                refine ⟨2304355120659189012872497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3072473494212252017163329 2304355120659189012872497)
                ·
                  refine ⟨1728266340494391759654373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2304355120659189012872497 1728266340494391759654373)
                  ·
                    refine ⟨324049938842698454935195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1728266340494391759654373 324049938842698454935195)
                    ·
                      rfl

theorem cell23_1893255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_1893255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893255 prefixEnd_1893255 := by exact prefixLift 1893255
  have htrace : WordTrace (prefixWord ++ tailWord_1893255) baseStart_1893255 baseEnd_1893255 := by
    simpa [prefixWord, tailWord_1893255, baseEnd_1893255] using wordTrace_append hprefix tailTrace_1893255
  have hstable : (prefixWord ++ tailWord_1893255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893255).length < 2 ^ (prefixWord ++ tailWord_1893255).sum := by decide
  have hdescent : baseEnd_1893255 < baseStart_1893255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893302 : List Nat := [5, 1, 4, 1, 1, 2, 9]
def baseStart_1893302 : Nat := 118140960795 + 1893302 * 2 ^ 59
def prefixEnd_1893302 : Nat := 4983230072969 + 3 ^ 40 * 1893302 * 2
def baseEnd_1893302 : Nat := 12002147532331563961949

theorem tailTrace_1893302 : CollatzResearch.WordTrace tailWord_1893302 prefixEnd_1893302 12002147532331563961949 := by
  unfold tailWord_1893302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315899811681104942717635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46036264657931786055654773 4315899811681104942717635)
  ·
    refine ⟨6473849717521657414076453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315899811681104942717635 6473849717521657414076453)
    ·
      refine ⟨1213846822035310765139335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6473849717521657414076453 1213846822035310765139335)
      ·
        refine ⟨1820770233052966147709003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213846822035310765139335 1820770233052966147709003)
        ·
          refine ⟨2731155349579449221563505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1820770233052966147709003 2731155349579449221563505)
          ·
            refine ⟨2048366512184586916172629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731155349579449221563505 2048366512184586916172629)
            ·
              refine ⟨12002147532331563961949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2048366512184586916172629 12002147532331563961949)
              ·
                rfl

theorem cell23_1893302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 9].length) (baseStart_1893302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893302 prefixEnd_1893302 := by exact prefixLift 1893302
  have htrace : WordTrace (prefixWord ++ tailWord_1893302) baseStart_1893302 baseEnd_1893302 := by
    simpa [prefixWord, tailWord_1893302, baseEnd_1893302] using wordTrace_append hprefix tailTrace_1893302
  have hstable : (prefixWord ++ tailWord_1893302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893302).length < 2 ^ (prefixWord ++ tailWord_1893302).sum := by decide
  have hdescent : baseEnd_1893302 < baseStart_1893302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893305 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 1, 3, 2]
def baseStart_1893305 : Nat := 118140960795 + 1893305 * 2 ^ 59
def prefixEnd_1893305 : Nat := 4983230072969 + 3 ^ 40 * 1893305 * 2
def baseEnd_1893305 : Nat := 972175490560820169180355

theorem tailTrace_1893305 : CollatzResearch.WordTrace tailWord_1893305 prefixEnd_1893305 972175490560820169180355 := by
  unfold tailWord_1893305
  simp only [CollatzResearch.WordTrace]
  refine ⟨69054506405886810595841369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46036337603924540397227579 69054506405886810595841369)
  ·
    refine ⟨51790879804415107946881027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69054506405886810595841369 51790879804415107946881027)
    ·
      refine ⟨77686319706622661920321541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51790879804415107946881027 77686319706622661920321541)
      ·
        refine ⟨14566184944991749110060289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77686319706622661920321541 14566184944991749110060289)
        ·
          refine ⟨10924638708743811832545217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14566184944991749110060289 10924638708743811832545217)
          ·
            refine ⟨8193479031557858874408913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10924638708743811832545217 8193479031557858874408913)
            ·
              refine ⟨6145109273668394155806685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8193479031557858874408913 6145109273668394155806685)
              ·
                refine ⟨2304415977625647808427507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6145109273668394155806685 2304415977625647808427507)
                ·
                  refine ⟨3456623966438471712641261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2304415977625647808427507 3456623966438471712641261)
                  ·
                    refine ⟨1296233987414426892240473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3456623966438471712641261 1296233987414426892240473)
                    ·
                      refine ⟨972175490560820169180355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296233987414426892240473 972175490560820169180355)
                      ·
                        rfl

theorem cell23_1893305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_1893305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893305 prefixEnd_1893305 := by exact prefixLift 1893305
  have htrace : WordTrace (prefixWord ++ tailWord_1893305) baseStart_1893305 baseEnd_1893305 := by
    simpa [prefixWord, tailWord_1893305, baseEnd_1893305] using wordTrace_append hprefix tailTrace_1893305
  have hstable : (prefixWord ++ tailWord_1893305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893305).length < 2 ^ (prefixWord ++ tailWord_1893305).sum := by decide
  have hdescent : baseEnd_1893305 < baseStart_1893305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893364 : List Nat := [2, 6, 2, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_1893364 : Nat := 118140960795 + 1893364 * 2 ^ 59
def prefixEnd_1893364 : Nat := 4983230072969 + 3 ^ 40 * 1893364 * 2
def baseEnd_1893364 : Nat := 972205785919435438342585

theorem tailTrace_1893364 : CollatzResearch.WordTrace tailWord_1893364 prefixEnd_1893364 972205785919435438342585 := by
  unfold tailWord_1893364
  simp only [CollatzResearch.WordTrace]
  refine ⟨34528329156336531836119573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46037772208448709114826097 34528329156336531836119573)
  ·
    refine ⟨1618515429203274929818105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34528329156336531836119573 1618515429203274929818105)
    ·
      refine ⟨1213886571902456197363579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1618515429203274929818105 1213886571902456197363579)
      ·
        refine ⟨1820829857853684296045369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213886571902456197363579 1820829857853684296045369)
        ·
          refine ⟨1365622393390263222034027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1820829857853684296045369 1365622393390263222034027)
          ·
            refine ⟨2048433590085394833051041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365622393390263222034027 2048433590085394833051041)
            ·
              refine ⟨1536325192564046124788281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048433590085394833051041 1536325192564046124788281)
              ·
                refine ⟨1152243894423034593591211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536325192564046124788281 1152243894423034593591211)
                ·
                  refine ⟨1728365841634551890386817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152243894423034593591211 1728365841634551890386817)
                  ·
                    refine ⟨1296274381225913917790113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1728365841634551890386817 1296274381225913917790113)
                    ·
                      refine ⟨972205785919435438342585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296274381225913917790113 972205785919435438342585)
                      ·
                        rfl

theorem cell23_1893364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_1893364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893364 prefixEnd_1893364 := by exact prefixLift 1893364
  have htrace : WordTrace (prefixWord ++ tailWord_1893364) baseStart_1893364 baseEnd_1893364 := by
    simpa [prefixWord, tailWord_1893364, baseEnd_1893364] using wordTrace_append hprefix tailTrace_1893364
  have hstable : (prefixWord ++ tailWord_1893364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893364).length < 2 ^ (prefixWord ++ tailWord_1893364).sum := by decide
  have hdescent : baseEnd_1893364 < baseStart_1893364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893381 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 5]
def baseStart_1893381 : Nat := 118140960795 + 1893381 * 2 ^ 59
def prefixEnd_1893381 : Nat := 4983230072969 + 3 ^ 40 * 1893381 * 2
def baseEnd_1893381 : Nat := 972214515090561871830005

theorem tailTrace_1893381 : CollatzResearch.WordTrace tailWord_1893381 prefixEnd_1893381 972214515090561871830005 := by
  unfold tailWord_1893381
  simp only [CollatzResearch.WordTrace]
  refine ⟨69057278353611475575607997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46038185569074317050405331 69057278353611475575607997)
  ·
    refine ⟨25896479382604303340852999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69057278353611475575607997 25896479382604303340852999)
    ·
      refine ⟨38844719073906455011279499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25896479382604303340852999 38844719073906455011279499)
      ·
        refine ⟨58267078610859682516919249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38844719073906455011279499 58267078610859682516919249)
        ·
          refine ⟨43700308958144761887689437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58267078610859682516919249 43700308958144761887689437)
          ·
            refine ⟨16387615859304285707883539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43700308958144761887689437 16387615859304285707883539)
            ·
              refine ⟨24581423788956428561825309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16387615859304285707883539 24581423788956428561825309)
              ·
                refine ⟨9218033920858660710684491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24581423788956428561825309 9218033920858660710684491)
                ·
                  refine ⟨13827050881287991066026737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9218033920858660710684491 13827050881287991066026737)
                  ·
                    refine ⟨10370288160965993299520053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13827050881287991066026737 10370288160965993299520053)
                    ·
                      refine ⟨972214515090561871830005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10370288160965993299520053 972214515090561871830005)
                      ·
                        rfl

theorem cell23_1893381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_1893381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893381 prefixEnd_1893381 := by exact prefixLift 1893381
  have htrace : WordTrace (prefixWord ++ tailWord_1893381) baseStart_1893381 baseEnd_1893381 := by
    simpa [prefixWord, tailWord_1893381, baseEnd_1893381] using wordTrace_append hprefix tailTrace_1893381
  have hstable : (prefixWord ++ tailWord_1893381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893381).length < 2 ^ (prefixWord ++ tailWord_1893381).sum := by decide
  have hdescent : baseEnd_1893381 < baseStart_1893381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893538 : List Nat := [3, 3, 1, 3, 13]
def baseStart_1893538 : Nat := 118140960795 + 1893538 * 2 ^ 59
def prefixEnd_1893538 : Nat := 4983230072969 + 3 ^ 40 * 1893538 * 2
def baseEnd_1893538 : Nat := 1333738177713741779927

theorem tailTrace_1893538 : CollatzResearch.WordTrace tailWord_1893538 prefixEnd_1893538 1333738177713741779927 := by
  unfold tailWord_1893538
  simp only [CollatzResearch.WordTrace]
  refine ⟨17265751153510672847268317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46042003076028460926048845 17265751153510672847268317)
  ·
    refine ⟨6474656682566502317725619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17265751153510672847268317 6474656682566502317725619)
    ·
      refine ⟨9711985023849753476588429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6474656682566502317725619 9711985023849753476588429)
      ·
        refine ⟨3641994383943657553720661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9711985023849753476588429 3641994383943657553720661)
        ·
          refine ⟨1333738177713741779927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 3641994383943657553720661 1333738177713741779927)
          ·
            rfl

theorem cell23_1893538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 13].length) (baseStart_1893538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893538 prefixEnd_1893538 := by exact prefixLift 1893538
  have htrace : WordTrace (prefixWord ++ tailWord_1893538) baseStart_1893538 baseEnd_1893538 := by
    simpa [prefixWord, tailWord_1893538, baseEnd_1893538] using wordTrace_append hprefix tailTrace_1893538
  have hstable : (prefixWord ++ tailWord_1893538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893538).length < 2 ^ (prefixWord ++ tailWord_1893538).sum := by decide
  have hdescent : baseEnd_1893538 < baseStart_1893538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893543 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 1, 1, 3]
def baseStart_1893543 : Nat := 118140960795 + 1893543 * 2 ^ 59
def prefixEnd_1893543 : Nat := 4983230072969 + 3 ^ 40 * 1893543 * 2
def baseEnd_1893543 : Nat := 972297698956590238004261

theorem tailTrace_1893543 : CollatzResearch.WordTrace tailWord_1893543 prefixEnd_1893543 972297698956590238004261 := by
  unfold tailWord_1893543
  simp only [CollatzResearch.WordTrace]
  refine ⟨69063186979024577243005283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46042124652683051495336855 69063186979024577243005283)
  ·
    refine ⟨103594780468536865864507925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69063186979024577243005283 103594780468536865864507925)
    ·
      refine ⟨4856005334462665587398809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103594780468536865864507925 4856005334462665587398809)
      ·
        refine ⟨3642004000846999190549107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4856005334462665587398809 3642004000846999190549107)
        ·
          refine ⟨5463006001270498785823661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3642004000846999190549107 5463006001270498785823661)
          ·
            refine ⟨2048627250476437044683873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5463006001270498785823661 2048627250476437044683873)
            ·
              refine ⟨1536470437857327783512905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2048627250476437044683873 1536470437857327783512905)
              ·
                refine ⟨1152352828392995837634679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1536470437857327783512905 1152352828392995837634679)
                ·
                  refine ⟨1728529242589493756452019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152352828392995837634679 1728529242589493756452019)
                  ·
                    refine ⟨2592793863884240634678029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1728529242589493756452019 2592793863884240634678029)
                    ·
                      refine ⟨972297698956590238004261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2592793863884240634678029 972297698956590238004261)
                      ·
                        rfl

theorem cell23_1893543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_1893543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893543 prefixEnd_1893543 := by exact prefixLift 1893543
  have htrace : WordTrace (prefixWord ++ tailWord_1893543) baseStart_1893543 baseEnd_1893543 := by
    simpa [prefixWord, tailWord_1893543, baseEnd_1893543] using wordTrace_append hprefix tailTrace_1893543
  have hstable : (prefixWord ++ tailWord_1893543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893543).length < 2 ^ (prefixWord ++ tailWord_1893543).sum := by decide
  have hdescent : baseEnd_1893543 < baseStart_1893543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893565 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1893565 : Nat := 118140960795 + 1893565 * 2 ^ 59
def prefixEnd_1893565 : Nat := 4983230072969 + 3 ^ 40 * 1893565 * 2
def baseEnd_1893565 : Nat := 972308995530989151929159

theorem tailTrace_1893565 : CollatzResearch.WordTrace tailWord_1893565 prefixEnd_1893565 972308995530989151929159 := by
  unfold tailWord_1893565
  simp only [CollatzResearch.WordTrace]
  refine ⟨69063989384944875000306149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46042659589963250000204099 69063989384944875000306149)
  ·
    refine ⟨12949498009677164062557403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69063989384944875000306149 12949498009677164062557403)
    ·
      refine ⟨19424247014515746093836105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12949498009677164062557403 19424247014515746093836105)
      ·
        refine ⟨14568185260886809570377079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19424247014515746093836105 14568185260886809570377079)
        ·
          refine ⟨21852277891330214355565619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14568185260886809570377079 21852277891330214355565619)
          ·
            refine ⟨32778416836995321533348429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21852277891330214355565619 32778416836995321533348429)
            ·
              refine ⟨12291906313873245575005661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32778416836995321533348429 12291906313873245575005661)
              ·
                refine ⟨4609464867702467090627123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12291906313873245575005661 4609464867702467090627123)
                ·
                  refine ⟨6914197301553700635940685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4609464867702467090627123 6914197301553700635940685)
                  ·
                    refine ⟨2592823988082637738477757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6914197301553700635940685 2592823988082637738477757)
                    ·
                      refine ⟨972308995530989151929159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2592823988082637738477757 972308995530989151929159)
                      ·
                        rfl

theorem cell23_1893565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1893565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893565 prefixEnd_1893565 := by exact prefixLift 1893565
  have htrace : WordTrace (prefixWord ++ tailWord_1893565) baseStart_1893565 baseEnd_1893565 := by
    simpa [prefixWord, tailWord_1893565, baseEnd_1893565] using wordTrace_append hprefix tailTrace_1893565
  have hstable : (prefixWord ++ tailWord_1893565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893565).length < 2 ^ (prefixWord ++ tailWord_1893565).sum := by decide
  have hdescent : baseEnd_1893565 < baseStart_1893565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893570 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_1893570 : Nat := 118140960795 + 1893570 * 2 ^ 59
def prefixEnd_1893570 : Nat := 4983230072969 + 3 ^ 40 * 1893570 * 2
def baseEnd_1893570 : Nat := 972311562934261632366637

theorem tailTrace_1893570 : CollatzResearch.WordTrace tailWord_1893570 prefixEnd_1893570 972311562934261632366637 := by
  unfold tailWord_1893570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17266042937481690213559541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46042781166617840569492109 17266042937481690213559541)
  ·
    refine ⟨1618691525388908457521207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17266042937481690213559541 1618691525388908457521207)
    ·
      refine ⟨2428037288083362686281811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1618691525388908457521207 2428037288083362686281811)
      ·
        refine ⟨3642055932125044029422717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2428037288083362686281811 3642055932125044029422717)
        ·
          refine ⟨1365770974546891511033519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3642055932125044029422717 1365770974546891511033519)
          ·
            refine ⟨2048656461820337266550279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1365770974546891511033519 2048656461820337266550279)
            ·
              refine ⟨3072984692730505899825419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048656461820337266550279 3072984692730505899825419)
              ·
                refine ⟨4609477039095758849738129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3072984692730505899825419 4609477039095758849738129)
                ·
                  refine ⟨3457107779321819137303597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609477039095758849738129 3457107779321819137303597)
                  ·
                    refine ⟨1296415417245682176488849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3457107779321819137303597 1296415417245682176488849)
                    ·
                      refine ⟨972311562934261632366637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296415417245682176488849 972311562934261632366637)
                      ·
                        rfl

theorem cell23_1893570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_1893570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893570 prefixEnd_1893570 := by exact prefixLift 1893570
  have htrace : WordTrace (prefixWord ++ tailWord_1893570) baseStart_1893570 baseEnd_1893570 := by
    simpa [prefixWord, tailWord_1893570, baseEnd_1893570] using wordTrace_append hprefix tailTrace_1893570
  have hstable : (prefixWord ++ tailWord_1893570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893570).length < 2 ^ (prefixWord ++ tailWord_1893570).sum := by decide
  have hdescent : baseEnd_1893570 < baseStart_1893570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893572 : List Nat := [2, 3, 3, 1, 3, 1, 3, 7]
def baseStart_1893572 : Nat := 118140960795 + 1893572 * 2 ^ 59
def prefixEnd_1893572 : Nat := 4983230072969 + 3 ^ 40 * 1893572 * 2
def baseEnd_1893572 : Nat := 36011577403539652760801

theorem tailTrace_1893572 : CollatzResearch.WordTrace tailWord_1893572 prefixEnd_1893572 36011577403539652760801 := by
  unfold tailWord_1893572
  simp only [CollatzResearch.WordTrace]
  refine ⟨34532122347959757597905485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46042829797279676797207313 34532122347959757597905485)
  ·
    refine ⟨12949545880484909099214557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34532122347959757597905485 12949545880484909099214557)
    ·
      refine ⟨4856079705181840912205459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12949545880484909099214557 4856079705181840912205459)
      ·
        refine ⟨7284119557772761368308189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856079705181840912205459 7284119557772761368308189)
        ·
          refine ⟨2731544834164785513115571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7284119557772761368308189 2731544834164785513115571)
          ·
            refine ⟨4097317251247178269673357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731544834164785513115571 4097317251247178269673357)
            ·
              refine ⟨1536493969217691851127509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4097317251247178269673357 1536493969217691851127509)
              ·
                refine ⟨36011577403539652760801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1536493969217691851127509 36011577403539652760801)
                ·
                  rfl

theorem cell23_1893572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 7].length) (baseStart_1893572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893572 prefixEnd_1893572 := by exact prefixLift 1893572
  have htrace : WordTrace (prefixWord ++ tailWord_1893572) baseStart_1893572 baseEnd_1893572 := by
    simpa [prefixWord, tailWord_1893572, baseEnd_1893572] using wordTrace_append hprefix tailTrace_1893572
  have hstable : (prefixWord ++ tailWord_1893572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893572).length < 2 ^ (prefixWord ++ tailWord_1893572).sum := by decide
  have hdescent : baseEnd_1893572 < baseStart_1893572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893692 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 2, 5]
def baseStart_1893692 : Nat := 118140960795 + 1893692 * 2 ^ 59
def prefixEnd_1893692 : Nat := 4983230072969 + 3 ^ 40 * 1893692 * 2
def baseEnd_1893692 : Nat := 324124735858036718347025

theorem tailTrace_1893692 : CollatzResearch.WordTrace tailWord_1893692 prefixEnd_1893692 324124735858036718347025 := by
  unfold tailWord_1893692
  simp only [CollatzResearch.WordTrace]
  refine ⟨34534310727742387845089665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46045747636989850460119553 34534310727742387845089665)
  ·
    refine ⟨25900733045806790883817249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34534310727742387845089665 25900733045806790883817249)
    ·
      refine ⟨19425549784355093162862937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25900733045806790883817249 19425549784355093162862937)
      ·
        refine ⟨14569162338266319872147203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19425549784355093162862937 14569162338266319872147203)
        ·
          refine ⟨21853743507399479808220805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14569162338266319872147203 21853743507399479808220805)
          ·
            refine ⟨4097576907637402464041401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21853743507399479808220805 4097576907637402464041401)
            ·
              refine ⟨3073182680728051848031051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4097576907637402464041401 3073182680728051848031051)
              ·
                refine ⟨4609774021092077772046577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3073182680728051848031051 4609774021092077772046577)
                ·
                  refine ⟨3457330515819058329034933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4609774021092077772046577 3457330515819058329034933)
                  ·
                    refine ⟨324124735858036718347025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3457330515819058329034933 324124735858036718347025)
                    ·
                      rfl

theorem cell23_1893692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_1893692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893692 prefixEnd_1893692 := by exact prefixLift 1893692
  have htrace : WordTrace (prefixWord ++ tailWord_1893692) baseStart_1893692 baseEnd_1893692 := by
    simpa [prefixWord, tailWord_1893692, baseEnd_1893692] using wordTrace_append hprefix tailTrace_1893692
  have hstable : (prefixWord ++ tailWord_1893692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893692).length < 2 ^ (prefixWord ++ tailWord_1893692).sum := by decide
  have hdescent : baseEnd_1893692 < baseStart_1893692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893712 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 2, 4, 2]
def baseStart_1893712 : Nat := 118140960795 + 1893712 * 2 ^ 59
def prefixEnd_1893712 : Nat := 4983230072969 + 3 ^ 40 * 1893712 * 2
def baseEnd_1893712 : Nat := 972384477187200076790983

theorem tailTrace_1893712 : CollatzResearch.WordTrace tailWord_1893712 prefixEnd_1893712 972384477187200076790983 := by
  unfold tailWord_1893712
  simp only [CollatzResearch.WordTrace]
  refine ⟨34534675457706159552953695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46046233943608212737271593 34534675457706159552953695)
  ·
    refine ⟨51802013186559239329430543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34534675457706159552953695 51802013186559239329430543)
    ·
      refine ⟨77703019779838858994145815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51802013186559239329430543 77703019779838858994145815)
      ·
        refine ⟨116554529669758288491218723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77703019779838858994145815 116554529669758288491218723)
        ·
          refine ⟨174831794504637432736828085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116554529669758288491218723 174831794504637432736828085)
          ·
            refine ⟨16390480734809759319077633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 174831794504637432736828085 16390480734809759319077633)
            ·
              refine ⟨12292860551107319489308225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16390480734809759319077633 12292860551107319489308225)
              ·
                refine ⟨9219645413330489616981169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12292860551107319489308225 9219645413330489616981169)
                ·
                  refine ⟨6914734059997867212735877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9219645413330489616981169 6914734059997867212735877)
                  ·
                    refine ⟨1296512636249600102387977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6914734059997867212735877 1296512636249600102387977)
                    ·
                      refine ⟨972384477187200076790983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296512636249600102387977 972384477187200076790983)
                      ·
                        rfl

theorem cell23_1893712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 2, 4, 2].length) (baseStart_1893712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893712 prefixEnd_1893712 := by exact prefixLift 1893712
  have htrace : WordTrace (prefixWord ++ tailWord_1893712) baseStart_1893712 baseEnd_1893712 := by
    simpa [prefixWord, tailWord_1893712, baseEnd_1893712] using wordTrace_append hprefix tailTrace_1893712
  have hstable : (prefixWord ++ tailWord_1893712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893712).length < 2 ^ (prefixWord ++ tailWord_1893712).sum := by decide
  have hdescent : baseEnd_1893712 < baseStart_1893712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893749 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1893749 : Nat := 118140960795 + 1893749 * 2 ^ 59
def prefixEnd_1893749 : Nat := 4983230072969 + 3 ^ 40 * 1893749 * 2
def baseEnd_1893749 : Nat := 972403475971416432028313

theorem tailTrace_1893749 : CollatzResearch.WordTrace tailWord_1893749 prefixEnd_1893749 972403475971416432028313 := by
  unfold tailWord_1893749
  simp only [CollatzResearch.WordTrace]
  refine ⟨69070700416278274425004301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46047133610852182950002867 69070700416278274425004301)
  ·
    refine ⟨25901512656104352909376613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69070700416278274425004301 25901512656104352909376613)
    ·
      refine ⟨4856533623019566170508115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25901512656104352909376613 4856533623019566170508115)
      ·
        refine ⟨7284800434529349255762173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856533623019566170508115 7284800434529349255762173)
        ·
          refine ⟨2731800162948505970910815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7284800434529349255762173 2731800162948505970910815)
          ·
            refine ⟨4097700244422758956366223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2731800162948505970910815 4097700244422758956366223)
            ·
              refine ⟨6146550366634138434549335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4097700244422758956366223 6146550366634138434549335)
              ·
                refine ⟨9219825549951207651824003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6146550366634138434549335 9219825549951207651824003)
                ·
                  refine ⟨13829738324926811477736005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9219825549951207651824003 13829738324926811477736005)
                  ·
                    refine ⟨2593075935923777152075501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13829738324926811477736005 2593075935923777152075501)
                    ·
                      refine ⟨972403475971416432028313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2593075935923777152075501 972403475971416432028313)
                      ·
                        rfl

theorem cell23_1893749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1893749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893749 prefixEnd_1893749 := by exact prefixLift 1893749
  have htrace : WordTrace (prefixWord ++ tailWord_1893749) baseStart_1893749 baseEnd_1893749 := by
    simpa [prefixWord, tailWord_1893749, baseEnd_1893749] using wordTrace_append hprefix tailTrace_1893749
  have hstable : (prefixWord ++ tailWord_1893749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893749).length < 2 ^ (prefixWord ++ tailWord_1893749).sum := by decide
  have hdescent : baseEnd_1893749 < baseStart_1893749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893769 : List Nat := [1, 2, 1, 1, 7, 2, 1, 2, 6]
def baseStart_1893769 : Nat := 118140960795 + 1893769 * 2 ^ 59
def prefixEnd_1893769 : Nat := 4983230072969 + 3 ^ 40 * 1893769 * 2
def baseEnd_1893769 : Nat := 108045971731611817086469

theorem tailTrace_1893769 : CollatzResearch.WordTrace tailWord_1893769 prefixEnd_1893769 108045971731611817086469 := by
  unfold tailWord_1893769
  simp only [CollatzResearch.WordTrace]
  refine ⟨69071429876205817840732361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46047619917470545227154907 69071429876205817840732361)
  ·
    refine ⟨51803572407154363380549271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69071429876205817840732361 51803572407154363380549271)
    ·
      refine ⟨77705358610731545070823907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51803572407154363380549271 77705358610731545070823907)
      ·
        refine ⟨116558037916097317606235861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77705358610731545070823907 116558037916097317606235861)
        ·
          refine ⟨2731829013658530881396153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 116558037916097317606235861 2731829013658530881396153)
          ·
            refine ⟨2048871760243898161047115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2731829013658530881396153 2048871760243898161047115)
            ·
              refine ⟨3073307640365847241570673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2048871760243898161047115 3073307640365847241570673)
              ·
                refine ⟨2304980730274385431178005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073307640365847241570673 2304980730274385431178005)
                ·
                  refine ⟨108045971731611817086469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2304980730274385431178005 108045971731611817086469)
                  ·
                    rfl

theorem cell23_1893769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 6].length) (baseStart_1893769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893769 prefixEnd_1893769 := by exact prefixLift 1893769
  have htrace : WordTrace (prefixWord ++ tailWord_1893769) baseStart_1893769 baseEnd_1893769 := by
    simpa [prefixWord, tailWord_1893769, baseEnd_1893769] using wordTrace_append hprefix tailTrace_1893769
  have hstable : (prefixWord ++ tailWord_1893769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893769).length < 2 ^ (prefixWord ++ tailWord_1893769).sum := by decide
  have hdescent : baseEnd_1893769 < baseStart_1893769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893789 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_1893789 : Nat := 118140960795 + 1893789 * 2 ^ 59
def prefixEnd_1893789 : Nat := 4983230072969 + 3 ^ 40 * 1893789 * 2
def baseEnd_1893789 : Nat := 972424015197596275528129

theorem tailTrace_1893789 : CollatzResearch.WordTrace tailWord_1893789 prefixEnd_1893789 972424015197596275528129 := by
  unfold tailWord_1893789
  simp only [CollatzResearch.WordTrace]
  refine ⟨69072159336133361256460421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46048106224088907504306947 69072159336133361256460421)
  ·
    refine ⟨12951029875525005235586329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69072159336133361256460421 12951029875525005235586329)
    ·
      refine ⟨9713272406643753926689747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12951029875525005235586329 9713272406643753926689747)
      ·
        refine ⟨14569908609965630890034621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9713272406643753926689747 14569908609965630890034621)
        ·
          refine ⟨5463715728737111583762983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14569908609965630890034621 5463715728737111583762983)
          ·
            refine ⟨8195573593105667375644475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463715728737111583762983 8195573593105667375644475)
            ·
              refine ⟨12293360389658501063466713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8195573593105667375644475 12293360389658501063466713)
              ·
                refine ⟨9220020292243875797600035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12293360389658501063466713 9220020292243875797600035)
                ·
                  refine ⟨13830030438365813696400053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9220020292243875797600035 13830030438365813696400053)
                  ·
                    refine ⟨1296565353596795034037505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13830030438365813696400053 1296565353596795034037505)
                    ·
                      refine ⟨972424015197596275528129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296565353596795034037505 972424015197596275528129)
                      ·
                        rfl

theorem cell23_1893789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_1893789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893789 prefixEnd_1893789 := by exact prefixLift 1893789
  have htrace : WordTrace (prefixWord ++ tailWord_1893789) baseStart_1893789 baseEnd_1893789 := by
    simpa [prefixWord, tailWord_1893789, baseEnd_1893789] using wordTrace_append hprefix tailTrace_1893789
  have hstable : (prefixWord ++ tailWord_1893789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893789).length < 2 ^ (prefixWord ++ tailWord_1893789).sum := by decide
  have hdescent : baseEnd_1893789 < baseStart_1893789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893799 : List Nat := [1, 1, 6, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1893799 : Nat := 118140960795 + 1893799 * 2 ^ 59
def prefixEnd_1893799 : Nat := 4983230072969 + 3 ^ 40 * 1893799 * 2
def baseEnd_1893799 : Nat := 324143050001380412134361

theorem tailTrace_1893799 : CollatzResearch.WordTrace tailWord_1893799 prefixEnd_1893799 324143050001380412134361 := by
  unfold tailWord_1893799
  simp only [CollatzResearch.WordTrace]
  refine ⟨69072524066097132964324451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46048349377398088642882967 69072524066097132964324451)
  ·
    refine ⟨103608786099145699446486677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69072524066097132964324451 103608786099145699446486677)
    ·
      refine ⟨4856661848397454661554063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103608786099145699446486677 4856661848397454661554063)
      ·
        refine ⟨7284992772596181992331095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4856661848397454661554063 7284992772596181992331095)
        ·
          refine ⟨10927489158894272988496643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7284992772596181992331095 10927489158894272988496643)
          ·
            refine ⟨16391233738341409482744965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10927489158894272988496643 16391233738341409482744965)
            ·
              refine ⟨3073356325939014278014681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16391233738341409482744965 3073356325939014278014681)
              ·
                refine ⟨2305017244454260708511011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073356325939014278014681 2305017244454260708511011)
                ·
                  refine ⟨3457525866681391062766517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305017244454260708511011 3457525866681391062766517)
                  ·
                    refine ⟨324143050001380412134361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3457525866681391062766517 324143050001380412134361)
                    ·
                      rfl

theorem cell23_1893799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1893799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893799 prefixEnd_1893799 := by exact prefixLift 1893799
  have htrace : WordTrace (prefixWord ++ tailWord_1893799) baseStart_1893799 baseEnd_1893799 := by
    simpa [prefixWord, tailWord_1893799, baseEnd_1893799] using wordTrace_append hprefix tailTrace_1893799
  have hstable : (prefixWord ++ tailWord_1893799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893799).length < 2 ^ (prefixWord ++ tailWord_1893799).sum := by decide
  have hdescent : baseEnd_1893799 < baseStart_1893799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893813 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_1893813 : Nat := 118140960795 + 1893813 * 2 ^ 59
def prefixEnd_1893813 : Nat := 4983230072969 + 3 ^ 40 * 1893813 * 2
def baseEnd_1893813 : Nat := 972436338733304181628019

theorem tailTrace_1893813 : CollatzResearch.WordTrace tailWord_1893813 prefixEnd_1893813 972436338733304181628019 := by
  unfold tailWord_1893813
  simp only [CollatzResearch.WordTrace]
  refine ⟨69073034688046413355334093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46048689792030942236889395 69073034688046413355334093)
  ·
    refine ⟨25902388008017405008250285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69073034688046413355334093 25902388008017405008250285)
    ·
      refine ⟨9713395503006526878093857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25902388008017405008250285 9713395503006526878093857)
      ·
        refine ⟨7285046627254895158570393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9713395503006526878093857 7285046627254895158570393)
        ·
          refine ⟨5463784970441171368927795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285046627254895158570393 5463784970441171368927795)
          ·
            refine ⟨8195677455661757053391693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5463784970441171368927795 8195677455661757053391693)
            ·
              refine ⟨3073379045873158895021885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8195677455661757053391693 3073379045873158895021885)
              ·
                refine ⟨1152517142202434585633207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3073379045873158895021885 1152517142202434585633207)
                ·
                  refine ⟨1728775713303651878449811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152517142202434585633207 1728775713303651878449811)
                  ·
                    refine ⟨2593163569955477817674717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1728775713303651878449811 2593163569955477817674717)
                    ·
                      refine ⟨972436338733304181628019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2593163569955477817674717 972436338733304181628019)
                      ·
                        rfl

theorem cell23_1893813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_1893813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893813 prefixEnd_1893813 := by exact prefixLift 1893813
  have htrace : WordTrace (prefixWord ++ tailWord_1893813) baseStart_1893813 baseEnd_1893813 := by
    simpa [prefixWord, tailWord_1893813, baseEnd_1893813] using wordTrace_append hprefix tailTrace_1893813
  have hstable : (prefixWord ++ tailWord_1893813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893813).length < 2 ^ (prefixWord ++ tailWord_1893813).sum := by decide
  have hdescent : baseEnd_1893813 < baseStart_1893813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893865 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 7]
def baseStart_1893865 : Nat := 118140960795 + 1893865 * 2 ^ 59
def prefixEnd_1893865 : Nat := 4983230072969 + 3 ^ 40 * 1893865 * 2
def baseEnd_1893865 : Nat := 972463039727337978177779

theorem tailTrace_1893865 : CollatzResearch.WordTrace tailWord_1893865 prefixEnd_1893865 972463039727337978177779 := by
  unfold tailWord_1893865
  simp only [CollatzResearch.WordTrace]
  refine ⟨69074931283858026236227049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46049954189238684157484699 69074931283858026236227049)
  ·
    refine ⟨51806198462893519677170287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69074931283858026236227049 51806198462893519677170287)
    ·
      refine ⟨77709297694340279515755431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51806198462893519677170287 77709297694340279515755431)
      ·
        refine ⟨116563946541510419273633147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77709297694340279515755431 116563946541510419273633147)
        ·
          refine ⟨174845919812265628910449721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116563946541510419273633147 174845919812265628910449721)
          ·
            refine ⟨131134439859199221682837291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174845919812265628910449721 131134439859199221682837291)
            ·
              refine ⟨196701659788798832524255937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131134439859199221682837291 196701659788798832524255937)
              ·
                refine ⟨147526244841599124393191953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196701659788798832524255937 147526244841599124393191953)
                ·
                  refine ⟨110644683631199343294893965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 147526244841599124393191953 110644683631199343294893965)
                  ·
                    refine ⟨41491756361699753735585237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110644683631199343294893965 41491756361699753735585237)
                    ·
                      refine ⟨972463039727337978177779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41491756361699753735585237 972463039727337978177779)
                      ·
                        rfl

theorem cell23_1893865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_1893865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893865 prefixEnd_1893865 := by exact prefixLift 1893865
  have htrace : WordTrace (prefixWord ++ tailWord_1893865) baseStart_1893865 baseEnd_1893865 := by
    simpa [prefixWord, tailWord_1893865, baseEnd_1893865] using wordTrace_append hprefix tailTrace_1893865
  have hstable : (prefixWord ++ tailWord_1893865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893865).length < 2 ^ (prefixWord ++ tailWord_1893865).sum := by decide
  have hdescent : baseEnd_1893865 < baseStart_1893865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893943 : List Nat := [1, 1, 3, 1, 2, 4, 3, 2, 2, 2, 2]
def baseStart_1893943 : Nat := 118140960795 + 1893943 * 2 ^ 59
def prefixEnd_1893943 : Nat := 4983230072969 + 3 ^ 40 * 1893943 * 2
def baseEnd_1893943 : Nat := 972503091218388673002421

theorem tailTrace_1893943 : CollatzResearch.WordTrace tailWord_1893943 prefixEnd_1893943 972503091218388673002421 := by
  unfold tailWord_1893943
  simp only [CollatzResearch.WordTrace]
  refine ⟨69077776177575445557566483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46051850785050297038377655 69077776177575445557566483)
  ·
    refine ⟨103616664266363168336349725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69077776177575445557566483 103616664266363168336349725)
    ·
      refine ⟨38856249099886188126131147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103616664266363168336349725 38856249099886188126131147)
      ·
        refine ⟨58284373649829282189196721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38856249099886188126131147 58284373649829282189196721)
        ·
          refine ⟨43713280237371961641897541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58284373649829282189196721 43713280237371961641897541)
          ·
            refine ⟨8196240044507242807855789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43713280237371961641897541 8196240044507242807855789)
            ·
              refine ⟨3073590016690216052945921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8196240044507242807855789 3073590016690216052945921)
              ·
                refine ⟨2305192512517662039709441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3073590016690216052945921 2305192512517662039709441)
                ·
                  refine ⟨1728894384388246529782081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2305192512517662039709441 1728894384388246529782081)
                  ·
                    refine ⟨1296670788291184897336561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1728894384388246529782081 1296670788291184897336561)
                    ·
                      refine ⟨972503091218388673002421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296670788291184897336561 972503091218388673002421)
                      ·
                        rfl

theorem cell23_1893943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 2, 2].length) (baseStart_1893943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893943 prefixEnd_1893943 := by exact prefixLift 1893943
  have htrace : WordTrace (prefixWord ++ tailWord_1893943) baseStart_1893943 baseEnd_1893943 := by
    simpa [prefixWord, tailWord_1893943, baseEnd_1893943] using wordTrace_append hprefix tailTrace_1893943
  have hstable : (prefixWord ++ tailWord_1893943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893943).length < 2 ^ (prefixWord ++ tailWord_1893943).sum := by decide
  have hdescent : baseEnd_1893943 < baseStart_1893943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1893962 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1893962 : Nat := 118140960795 + 1893962 * 2 ^ 59
def prefixEnd_1893962 : Nat := 4983230072969 + 3 ^ 40 * 1893962 * 2
def baseEnd_1893962 : Nat := 324170949116941366221611

theorem tailTrace_1893962 : CollatzResearch.WordTrace tailWord_1893962 prefixEnd_1893962 324170949116941366221611 := by
  unfold tailWord_1893962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17269617291126652950627035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46052312776337741201672093 17269617291126652950627035)
  ·
    refine ⟨25904425936689979425940553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17269617291126652950627035 25904425936689979425940553)
    ·
      refine ⟨19428319452517484569455415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25904425936689979425940553 19428319452517484569455415)
      ·
        refine ⟨29142479178776226854183123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19428319452517484569455415 29142479178776226854183123)
        ·
          refine ⟨43713718768164340281274685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29142479178776226854183123 43713718768164340281274685)
          ·
            refine ⟨16392644538061627605478007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43713718768164340281274685 16392644538061627605478007)
            ·
              refine ⟨24588966807092441408217011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16392644538061627605478007 24588966807092441408217011)
              ·
                refine ⟨36883450210638662112325517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24588966807092441408217011 36883450210638662112325517)
                ·
                  refine ⟨13831293828989498292122069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36883450210638662112325517 13831293828989498292122069)
                  ·
                    refine ⟨324170949116941366221611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13831293828989498292122069 324170949116941366221611)
                    ·
                      rfl

theorem cell23_1893962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1893962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1893962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1893962 prefixEnd_1893962 := by exact prefixLift 1893962
  have htrace : WordTrace (prefixWord ++ tailWord_1893962) baseStart_1893962 baseEnd_1893962 := by
    simpa [prefixWord, tailWord_1893962, baseEnd_1893962] using wordTrace_append hprefix tailTrace_1893962
  have hstable : (prefixWord ++ tailWord_1893962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1893962).length < 2 ^ (prefixWord ++ tailWord_1893962).sum := by decide
  have hdescent : baseEnd_1893962 < baseStart_1893962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1893962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894006 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1894006 : Nat := 118140960795 + 1894006 * 2 ^ 59
def prefixEnd_1894006 : Nat := 4983230072969 + 3 ^ 40 * 1894006 * 2
def baseEnd_1894006 : Nat := 972535440499621926514631

theorem tailTrace_1894006 : CollatzResearch.WordTrace tailWord_1894006 prefixEnd_1894006 972535440499621926514631 := by
  unfold tailWord_1894006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317504623521700457319367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46053382650898138211406581 4317504623521700457319367)
  ·
    refine ⟨6476256935282550685979051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4317504623521700457319367 6476256935282550685979051)
    ·
      refine ⟨9714385402923826028968577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6476256935282550685979051 9714385402923826028968577)
      ·
        refine ⟨7285789052192869521726433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9714385402923826028968577 7285789052192869521726433)
        ·
          refine ⟨5464341789144652141294825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7285789052192869521726433 5464341789144652141294825)
          ·
            refine ⟨4098256341858489105971119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5464341789144652141294825 4098256341858489105971119)
            ·
              refine ⟨6147384512787733658956679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098256341858489105971119 6147384512787733658956679)
              ·
                refine ⟨9221076769181600488435019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147384512787733658956679 9221076769181600488435019)
                ·
                  refine ⟨13831615153772400732652529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9221076769181600488435019 13831615153772400732652529)
                  ·
                    refine ⟨10373711365329300549489397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13831615153772400732652529 10373711365329300549489397)
                    ·
                      refine ⟨972535440499621926514631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10373711365329300549489397 972535440499621926514631)
                      ·
                        rfl

theorem cell23_1894006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1894006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894006 prefixEnd_1894006 := by exact prefixLift 1894006
  have htrace : WordTrace (prefixWord ++ tailWord_1894006) baseStart_1894006 baseEnd_1894006 := by
    simpa [prefixWord, tailWord_1894006, baseEnd_1894006] using wordTrace_append hprefix tailTrace_1894006
  have hstable : (prefixWord ++ tailWord_1894006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894006).length < 2 ^ (prefixWord ++ tailWord_1894006).sum := by decide
  have hdescent : baseEnd_1894006 < baseStart_1894006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894019 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 3]
def baseStart_1894019 : Nat := 118140960795 + 1894019 * 2 ^ 59
def prefixEnd_1894019 : Nat := 4983230072969 + 3 ^ 40 * 1894019 * 2
def baseEnd_1894019 : Nat := 972542115748130375652071

theorem tailTrace_1894019 : CollatzResearch.WordTrace tailWord_1894019 prefixEnd_1894019 972542115748130375652071 := by
  unfold tailWord_1894019
  simp only [CollatzResearch.WordTrace]
  refine ⟨69080548125300110537333111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46053698750200073691555407 69080548125300110537333111)
  ·
    refine ⟨103620822187950165805999667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69080548125300110537333111 103620822187950165805999667)
    ·
      refine ⟨155431233281925248708999501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103620822187950165805999667 155431233281925248708999501)
      ·
        refine ⟨58286712480721968265874813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155431233281925248708999501 58286712480721968265874813)
        ·
          refine ⟨21857517180270738099703055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58286712480721968265874813 21857517180270738099703055)
          ·
            refine ⟨32786275770406107149554583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21857517180270738099703055 32786275770406107149554583)
            ·
              refine ⟨49179413655609160724331875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32786275770406107149554583 49179413655609160724331875)
              ·
                refine ⟨73769120483413741086497813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49179413655609160724331875 73769120483413741086497813)
                ·
                  refine ⟨3457927522660019113429585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73769120483413741086497813 3457927522660019113429585)
                  ·
                    refine ⟨2593445641995014335072189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3457927522660019113429585 2593445641995014335072189)
                    ·
                      refine ⟨972542115748130375652071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2593445641995014335072189 972542115748130375652071)
                      ·
                        rfl

theorem cell23_1894019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_1894019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894019 prefixEnd_1894019 := by exact prefixLift 1894019
  have htrace : WordTrace (prefixWord ++ tailWord_1894019) baseStart_1894019 baseEnd_1894019 := by
    simpa [prefixWord, tailWord_1894019, baseEnd_1894019] using wordTrace_append hprefix tailTrace_1894019
  have hstable : (prefixWord ++ tailWord_1894019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894019).length < 2 ^ (prefixWord ++ tailWord_1894019).sum := by decide
  have hdescent : baseEnd_1894019 < baseStart_1894019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894116 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1894116 : Nat := 118140960795 + 1894116 * 2 ^ 59
def prefixEnd_1894116 : Nat := 4983230072969 + 3 ^ 40 * 1894116 * 2
def baseEnd_1894116 : Nat := 324197307790538832046375

theorem tailTrace_1894116 : CollatzResearch.WordTrace tailWord_1894116 prefixEnd_1894116 324197307790538832046375 := by
  unfold tailWord_1894116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34542043002974348051807101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46056057337299130735742801 34542043002974348051807101)
  ·
    refine ⟨12953266126115380519427663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34542043002974348051807101 12953266126115380519427663)
    ·
      refine ⟨19429899189173070779141495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12953266126115380519427663 19429899189173070779141495)
      ·
        refine ⟨29144848783759606168712243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19429899189173070779141495 29144848783759606168712243)
        ·
          refine ⟨43717273175639409253068365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29144848783759606168712243 43717273175639409253068365)
          ·
            refine ⟨16393977440864778469900637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43717273175639409253068365 16393977440864778469900637)
            ·
              refine ⟨6147741540324291926212739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16393977440864778469900637 6147741540324291926212739)
              ·
                refine ⟨9221612310486437889319109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6147741540324291926212739 9221612310486437889319109)
                ·
                  refine ⟨1729052308216207104247333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9221612310486437889319109 1729052308216207104247333)
                  ·
                    refine ⟨324197307790538832046375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729052308216207104247333 324197307790538832046375)
                    ·
                      rfl

theorem cell23_1894116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1894116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894116 prefixEnd_1894116 := by exact prefixLift 1894116
  have htrace : WordTrace (prefixWord ++ tailWord_1894116) baseStart_1894116 baseEnd_1894116 := by
    simpa [prefixWord, tailWord_1894116, baseEnd_1894116] using wordTrace_append hprefix tailTrace_1894116
  have hstable : (prefixWord ++ tailWord_1894116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894116).length < 2 ^ (prefixWord ++ tailWord_1894116).sum := by decide
  have hdescent : baseEnd_1894116 < baseStart_1894116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894123 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 3, 2, 2]
def baseStart_1894123 : Nat := 118140960795 + 1894123 * 2 ^ 59
def prefixEnd_1894123 : Nat := 4983230072969 + 3 ^ 40 * 1894123 * 2
def baseEnd_1894123 : Nat := 972595517736197968751593

theorem tailTrace_1894123 : CollatzResearch.WordTrace tailWord_1894123 prefixEnd_1894123 972595517736197968751593 := by
  unfold tailWord_1894123
  simp only [CollatzResearch.WordTrace]
  refine ⟨69084341316923336299119023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46056227544615557532746015 69084341316923336299119023)
  ·
    refine ⟨103626511975385004448678535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69084341316923336299119023 103626511975385004448678535)
    ·
      refine ⟨155439767963077506673017803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103626511975385004448678535 155439767963077506673017803)
      ·
        refine ⟨233159651944616260009526705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155439767963077506673017803 233159651944616260009526705)
        ·
          refine ⟨174869738958462195007145029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233159651944616260009526705 174869738958462195007145029)
          ·
            refine ⟨32788076054711661563839693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 174869738958462195007145029 32788076054711661563839693)
            ·
              refine ⟨12295528520516873086439885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32788076054711661563839693 12295528520516873086439885)
              ·
                refine ⟨4610823195193827407414957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12295528520516873086439885 4610823195193827407414957)
                ·
                  refine ⟨1729058698197685277780609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4610823195193827407414957 1729058698197685277780609)
                  ·
                    refine ⟨1296794023648263958335457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1729058698197685277780609 1296794023648263958335457)
                    ·
                      refine ⟨972595517736197968751593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296794023648263958335457 972595517736197968751593)
                      ·
                        rfl

theorem cell23_1894123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 2, 2].length) (baseStart_1894123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894123 prefixEnd_1894123 := by exact prefixLift 1894123
  have htrace : WordTrace (prefixWord ++ tailWord_1894123) baseStart_1894123 baseEnd_1894123 := by
    simpa [prefixWord, tailWord_1894123, baseEnd_1894123] using wordTrace_append hprefix tailTrace_1894123
  have hstable : (prefixWord ++ tailWord_1894123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894123).length < 2 ^ (prefixWord ++ tailWord_1894123).sum := by decide
  have hdescent : baseEnd_1894123 < baseStart_1894123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894126 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1894126 : Nat := 118140960795 + 1894126 * 2 ^ 59
def prefixEnd_1894126 : Nat := 4983230072969 + 3 ^ 40 * 1894126 * 2
def baseEnd_1894126 : Nat := 972597058178161457014079

theorem tailTrace_1894126 : CollatzResearch.WordTrace tailWord_1894126 prefixEnd_1894126 972597058178161457014079 := by
  unfold tailWord_1894126
  simp only [CollatzResearch.WordTrace]
  refine ⟨8635556341989058476434779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46056300490608311874318821 8635556341989058476434779)
  ·
    refine ⟨12953334512983587714652169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8635556341989058476434779 12953334512983587714652169)
    ·
      refine ⟨9715000884737690785989127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12953334512983587714652169 9715000884737690785989127)
      ·
        refine ⟨14572501327106536178983691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9715000884737690785989127 14572501327106536178983691)
        ·
          refine ⟨21858751990659804268475537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14572501327106536178983691 21858751990659804268475537)
          ·
            refine ⟨16394063992994853201356653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21858751990659804268475537 16394063992994853201356653)
            ·
              refine ⟨6147773997373069950508745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16394063992994853201356653 6147773997373069950508745)
              ·
                refine ⟨4610830498029802462881559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6147773997373069950508745 4610830498029802462881559)
                ·
                  refine ⟨6916245747044703694322339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610830498029802462881559 6916245747044703694322339)
                  ·
                    refine ⟨10374368620567055541483509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6916245747044703694322339 10374368620567055541483509)
                    ·
                      refine ⟨972597058178161457014079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10374368620567055541483509 972597058178161457014079)
                      ·
                        rfl

theorem cell23_1894126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1894126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894126 prefixEnd_1894126 := by exact prefixLift 1894126
  have htrace : WordTrace (prefixWord ++ tailWord_1894126) baseStart_1894126 baseEnd_1894126 := by
    simpa [prefixWord, tailWord_1894126, baseEnd_1894126] using wordTrace_append hprefix tailTrace_1894126
  have hstable : (prefixWord ++ tailWord_1894126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894126).length < 2 ^ (prefixWord ++ tailWord_1894126).sum := by decide
  have hdescent : baseEnd_1894126 < baseStart_1894126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894146 : List Nat := [3, 4, 1, 1, 1, 1, 3, 9]
def baseStart_1894146 : Nat := 118140960795 + 1894146 * 2 ^ 59
def prefixEnd_1894146 : Nat := 4983230072969 + 3 ^ 40 * 1894146 * 2
def baseEnd_1894146 : Nat := 36022493621898199213481

theorem tailTrace_1894146 : CollatzResearch.WordTrace tailWord_1894146 prefixEnd_1894146 36022493621898199213481 := by
  unfold tailWord_1894146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17271295048960002806801573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46056786797226674151470861 17271295048960002806801573)
  ·
    refine ⟨3238367821680000526275295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17271295048960002806801573 3238367821680000526275295)
    ·
      refine ⟨4857551732520000789412943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238367821680000526275295 4857551732520000789412943)
      ·
        refine ⟨7286327598780001184119415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857551732520000789412943 7286327598780001184119415)
        ·
          refine ⟨10929491398170001776179123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7286327598780001184119415 10929491398170001776179123)
          ·
            refine ⟨16394237097255002664268685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10929491398170001776179123 16394237097255002664268685)
            ·
              refine ⟨6147838911470625999100757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16394237097255002664268685 6147838911470625999100757)
              ·
                refine ⟨36022493621898199213481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6147838911470625999100757 36022493621898199213481)
                ·
                  rfl

theorem cell23_1894146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_1894146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894146 prefixEnd_1894146 := by exact prefixLift 1894146
  have htrace : WordTrace (prefixWord ++ tailWord_1894146) baseStart_1894146 baseEnd_1894146 := by
    simpa [prefixWord, tailWord_1894146, baseEnd_1894146] using wordTrace_append hprefix tailTrace_1894146
  have hstable : (prefixWord ++ tailWord_1894146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894146).length < 2 ^ (prefixWord ++ tailWord_1894146).sum := by decide
  have hdescent : baseEnd_1894146 < baseStart_1894146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894156 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1894156 : Nat := 118140960795 + 1894156 * 2 ^ 59
def prefixEnd_1894156 : Nat := 4983230072969 + 3 ^ 40 * 1894156 * 2
def baseEnd_1894156 : Nat := 972612462597796339638941

theorem tailTrace_1894156 : CollatzResearch.WordTrace tailWord_1894156 prefixEnd_1894156 972612462597796339638941 := by
  unfold tailWord_1894156
  simp only [CollatzResearch.WordTrace]
  refine ⟨34542772462901891467535161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46057029950535855290046881 34542772462901891467535161)
  ·
    refine ⟨25907079347176418600651371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34542772462901891467535161 25907079347176418600651371)
    ·
      refine ⟨38860619020764627900977057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25907079347176418600651371 38860619020764627900977057)
      ·
        refine ⟨29145464265573470925732793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38860619020764627900977057 29145464265573470925732793)
        ·
          refine ⟨21859098199180103194299595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29145464265573470925732793 21859098199180103194299595)
          ·
            refine ⟨32788647298770154791449393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21859098199180103194299595 32788647298770154791449393)
            ·
              refine ⟨24591485474077616093587045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32788647298770154791449393 24591485474077616093587045)
              ·
                refine ⟨4610903526389553017547571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24591485474077616093587045 4610903526389553017547571)
                ·
                  refine ⟨6916355289584329526321357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4610903526389553017547571 6916355289584329526321357)
                  ·
                    refine ⟨2593633233594123572370509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6916355289584329526321357 2593633233594123572370509)
                    ·
                      refine ⟨972612462597796339638941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2593633233594123572370509 972612462597796339638941)
                      ·
                        rfl

theorem cell23_1894156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1894156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894156 prefixEnd_1894156 := by exact prefixLift 1894156
  have htrace : WordTrace (prefixWord ++ tailWord_1894156) baseStart_1894156 baseEnd_1894156 := by
    simpa [prefixWord, tailWord_1894156, baseEnd_1894156] using wordTrace_append hprefix tailTrace_1894156
  have hstable : (prefixWord ++ tailWord_1894156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894156).length < 2 ^ (prefixWord ++ tailWord_1894156).sum := by decide
  have hdescent : baseEnd_1894156 < baseStart_1894156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894200 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 1, 3, 2]
def baseStart_1894200 : Nat := 118140960795 + 1894200 * 2 ^ 59
def prefixEnd_1894200 : Nat := 4983230072969 + 3 ^ 40 * 1894200 * 2
def baseEnd_1894200 : Nat := 972635055746594167488739

theorem tailTrace_1894200 : CollatzResearch.WordTrace tailWord_1894200 prefixEnd_1894200 972635055746594167488739 := by
  unfold tailWord_1894200
  simp only [CollatzResearch.WordTrace]
  refine ⟨34543574868822189224836027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46058099825096252299781369 34543574868822189224836027)
  ·
    refine ⟨51815362303233283837254041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34543574868822189224836027 51815362303233283837254041)
    ·
      refine ⟨38861521727424962877940531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51815362303233283837254041 38861521727424962877940531)
      ·
        refine ⟨58292282591137444316910797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38861521727424962877940531 58292282591137444316910797)
        ·
          refine ⟨21859605971676541618841549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58292282591137444316910797 21859605971676541618841549)
          ·
            refine ⟨8197352239378703107065581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21859605971676541618841549 8197352239378703107065581)
            ·
              refine ⟨3074007089767013665149593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8197352239378703107065581 3074007089767013665149593)
              ·
                refine ⟨2305505317325260248862195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074007089767013665149593 2305505317325260248862195)
                ·
                  refine ⟨3458257975987890373293293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305505317325260248862195 3458257975987890373293293)
                  ·
                    refine ⟨1296846740995458889984985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458257975987890373293293 1296846740995458889984985)
                    ·
                      refine ⟨972635055746594167488739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296846740995458889984985 972635055746594167488739)
                      ·
                        rfl

theorem cell23_1894200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 1, 3, 2].length) (baseStart_1894200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894200 prefixEnd_1894200 := by exact prefixLift 1894200
  have htrace : WordTrace (prefixWord ++ tailWord_1894200) baseStart_1894200 baseEnd_1894200 := by
    simpa [prefixWord, tailWord_1894200, baseEnd_1894200] using wordTrace_append hprefix tailTrace_1894200
  have hstable : (prefixWord ++ tailWord_1894200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894200).length < 2 ^ (prefixWord ++ tailWord_1894200).sum := by decide
  have hdescent : baseEnd_1894200 < baseStart_1894200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894213 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 1, 4, 2]
def baseStart_1894213 : Nat := 118140960795 + 1894213 * 2 ^ 59
def prefixEnd_1894213 : Nat := 4983230072969 + 3 ^ 40 * 1894213 * 2
def baseEnd_1894213 : Nat := 972641730995102616626179

theorem tailTrace_1894213 : CollatzResearch.WordTrace tailWord_1894213 prefixEnd_1894213 972641730995102616626179 := by
  unfold tailWord_1894213
  simp only [CollatzResearch.WordTrace]
  refine ⟨69087623886597281669895293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46058415924398187779930195 69087623886597281669895293)
  ·
    refine ⟨25907858957473980626210735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69087623886597281669895293 25907858957473980626210735)
    ·
      refine ⟨38861788436210970939316103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25907858957473980626210735 38861788436210970939316103)
      ·
        refine ⟨58292682654316456408974155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38861788436210970939316103 58292682654316456408974155)
        ·
          refine ⟨87439023981474684613461233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58292682654316456408974155 87439023981474684613461233)
          ·
            refine ⟨65579267986106013460095925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87439023981474684613461233 65579267986106013460095925)
            ·
              refine ⟨6148056373697438761883993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65579267986106013460095925 6148056373697438761883993)
              ·
                refine ⟨4611042280273079071412995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6148056373697438761883993 4611042280273079071412995)
                ·
                  refine ⟨6916563420409618607119493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4611042280273079071412995 6916563420409618607119493)
                  ·
                    refine ⟨1296855641326803488834905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6916563420409618607119493 1296855641326803488834905)
                    ·
                      refine ⟨972641730995102616626179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1296855641326803488834905 972641730995102616626179)
                      ·
                        rfl

theorem cell23_1894213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 4, 2].length) (baseStart_1894213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894213 prefixEnd_1894213 := by exact prefixLift 1894213
  have htrace : WordTrace (prefixWord ++ tailWord_1894213) baseStart_1894213 baseEnd_1894213 := by
    simpa [prefixWord, tailWord_1894213, baseEnd_1894213] using wordTrace_append hprefix tailTrace_1894213
  have hstable : (prefixWord ++ tailWord_1894213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894213).length < 2 ^ (prefixWord ++ tailWord_1894213).sum := by decide
  have hdescent : baseEnd_1894213 < baseStart_1894213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894216 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1894216 : Nat := 118140960795 + 1894216 * 2 ^ 59
def prefixEnd_1894216 : Nat := 4983230072969 + 3 ^ 40 * 1894216 * 2
def baseEnd_1894216 : Nat := 972643271437066104888665

theorem tailTrace_1894216 : CollatzResearch.WordTrace tailWord_1894216 prefixEnd_1894216 972643271437066104888665 := by
  unfold tailWord_1894216
  simp only [CollatzResearch.WordTrace]
  refine ⟨34543866652793206591127251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46058488870390942121503001 34543866652793206591127251)
  ·
    refine ⟨51815799979189809886690877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34543866652793206591127251 51815799979189809886690877)
    ·
      refine ⟨19430924992196178707509079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51815799979189809886690877 19430924992196178707509079)
      ·
        refine ⟨29146387488294268061263619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19430924992196178707509079 29146387488294268061263619)
        ·
          refine ⟨43719581232441402091895429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29146387488294268061263619 43719581232441402091895429)
          ·
            refine ⟨8197421481082762892230393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43719581232441402091895429 8197421481082762892230393)
            ·
              refine ⟨6148066110812072169172795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8197421481082762892230393 6148066110812072169172795)
              ·
                refine ⟨9222099166218108253759193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148066110812072169172795 9222099166218108253759193)
                ·
                  refine ⟨6916574374663581190319395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222099166218108253759193 6916574374663581190319395)
                  ·
                    refine ⟨10374861561995371785479093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6916574374663581190319395 10374861561995371785479093)
                    ·
                      refine ⟨972643271437066104888665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10374861561995371785479093 972643271437066104888665)
                      ·
                        rfl

theorem cell23_1894216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1894216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894216 prefixEnd_1894216 := by exact prefixLift 1894216
  have htrace : WordTrace (prefixWord ++ tailWord_1894216) baseStart_1894216 baseEnd_1894216 := by
    simpa [prefixWord, tailWord_1894216, baseEnd_1894216] using wordTrace_append hprefix tailTrace_1894216
  have hstable : (prefixWord ++ tailWord_1894216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894216).length < 2 ^ (prefixWord ++ tailWord_1894216).sum := by decide
  have hdescent : baseEnd_1894216 < baseStart_1894216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894243 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 4]
def baseStart_1894243 : Nat := 118140960795 + 1894243 * 2 ^ 59
def prefixEnd_1894243 : Nat := 4983230072969 + 3 ^ 40 * 1894243 * 2
def baseEnd_1894243 : Nat := 972657135414737499251041

theorem tailTrace_1894243 : CollatzResearch.WordTrace tailWord_1894243 prefixEnd_1894243 972657135414737499251041 := by
  unfold tailWord_1894243
  simp only [CollatzResearch.WordTrace]
  refine ⟨69088718076488596793487383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46059145384325731195658255 69088718076488596793487383)
  ·
    refine ⟨103633077114732895190231075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69088718076488596793487383 103633077114732895190231075)
    ·
      refine ⟨155449615672099342785346613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103633077114732895190231075 155449615672099342785346613)
      ·
        refine ⟨14573401469259313386126245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155449615672099342785346613 14573401469259313386126245)
        ·
          refine ⟨2732512775486121259898671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14573401469259313386126245 2732512775486121259898671)
          ·
            refine ⟨4098769163229181889848007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2732512775486121259898671 4098769163229181889848007)
            ·
              refine ⟨6148153744843772834772011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4098769163229181889848007 6148153744843772834772011)
              ·
                refine ⟨9222230617265659252158017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6148153744843772834772011 9222230617265659252158017)
                ·
                  refine ⟨6916672962949244439118513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9222230617265659252158017 6916672962949244439118513)
                  ·
                    refine ⟨5187504722211933329338885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6916672962949244439118513 5187504722211933329338885)
                    ·
                      refine ⟨972657135414737499251041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5187504722211933329338885 972657135414737499251041)
                      ·
                        rfl

theorem cell23_1894243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_1894243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894243 prefixEnd_1894243 := by exact prefixLift 1894243
  have htrace : WordTrace (prefixWord ++ tailWord_1894243) baseStart_1894243 baseEnd_1894243 := by
    simpa [prefixWord, tailWord_1894243, baseEnd_1894243] using wordTrace_append hprefix tailTrace_1894243
  have hstable : (prefixWord ++ tailWord_1894243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894243).length < 2 ^ (prefixWord ++ tailWord_1894243).sum := by decide
  have hdescent : baseEnd_1894243 < baseStart_1894243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894276 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1894276 : Nat := 118140960795 + 1894276 * 2 ^ 59
def prefixEnd_1894276 : Nat := 4983230072969 + 3 ^ 40 * 1894276 * 2
def baseEnd_1894276 : Nat := 972674080276335870138389

theorem tailTrace_1894276 : CollatzResearch.WordTrace tailWord_1894276 prefixEnd_1894276 972674080276335870138389 := by
  unfold tailWord_1894276
  simp only [CollatzResearch.WordTrace]
  refine ⟨34544960842684521714719341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46059947790246028952959121 34544960842684521714719341)
  ·
    refine ⟨12954360316006695643019753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34544960842684521714719341 12954360316006695643019753)
    ·
      refine ⟨9715770237005021732264815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12954360316006695643019753 9715770237005021732264815)
      ·
        refine ⟨14573655355507532598397223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9715770237005021732264815 14573655355507532598397223)
        ·
          refine ⟨21860483033261298897595835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14573655355507532598397223 21860483033261298897595835)
          ·
            refine ⟨32790724549891948346393753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21860483033261298897595835 32790724549891948346393753)
            ·
              refine ⟨24593043412418961259795315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32790724549891948346393753 24593043412418961259795315)
              ·
                refine ⟨36889565118628441889692973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24593043412418961259795315 36889565118628441889692973)
                ·
                  refine ⟨13833586919485665708634865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36889565118628441889692973 13833586919485665708634865)
                  ·
                    refine ⟨10375190189614249281476149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13833586919485665708634865 10375190189614249281476149)
                    ·
                      refine ⟨972674080276335870138389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10375190189614249281476149 972674080276335870138389)
                      ·
                        rfl

theorem cell23_1894276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1894276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894276 prefixEnd_1894276 := by exact prefixLift 1894276
  have htrace : WordTrace (prefixWord ++ tailWord_1894276) baseStart_1894276 baseEnd_1894276 := by
    simpa [prefixWord, tailWord_1894276, baseEnd_1894276] using wordTrace_append hprefix tailTrace_1894276
  have hstable : (prefixWord ++ tailWord_1894276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894276).length < 2 ^ (prefixWord ++ tailWord_1894276).sum := by decide
  have hdescent : baseEnd_1894276 < baseStart_1894276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894323 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 3]
def baseStart_1894323 : Nat := 118140960795 + 1894323 * 2 ^ 59
def prefixEnd_1894323 : Nat := 4983230072969 + 3 ^ 40 * 1894323 * 2
def baseEnd_1894323 : Nat := 972698213867097186250673

theorem tailTrace_1894323 : CollatzResearch.WordTrace tailWord_1894323 prefixEnd_1894323 972698213867097186250673 := by
  unfold tailWord_1894323
  simp only [CollatzResearch.WordTrace]
  refine ⟨69091635916198770456399623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46061090610799180304266415 69091635916198770456399623)
  ·
    refine ⟨103637453874298155684599435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69091635916198770456399623 103637453874298155684599435)
    ·
      refine ⟨155456180811447233526899153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103637453874298155684599435 155456180811447233526899153)
      ·
        refine ⟨116592135608585425145174365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155456180811447233526899153 116592135608585425145174365)
        ·
          refine ⟨43722050853219534429440387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116592135608585425145174365 43722050853219534429440387)
          ·
            refine ⟨65583076279829301644160581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43722050853219534429440387 65583076279829301644160581)
            ·
              refine ⟨12296826802467994058280109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65583076279829301644160581 12296826802467994058280109)
              ·
                refine ⟨4611310050925497771855041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12296826802467994058280109 4611310050925497771855041)
                ·
                  refine ⟨3458482538194123328891281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4611310050925497771855041 3458482538194123328891281)
                  ·
                    refine ⟨2593861903645592496668461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3458482538194123328891281 2593861903645592496668461)
                    ·
                      refine ⟨972698213867097186250673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2593861903645592496668461 972698213867097186250673)
                      ·
                        rfl

theorem cell23_1894323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_1894323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894323 prefixEnd_1894323 := by exact prefixLift 1894323
  have htrace : WordTrace (prefixWord ++ tailWord_1894323) baseStart_1894323 baseEnd_1894323 := by
    simpa [prefixWord, tailWord_1894323, baseEnd_1894323] using wordTrace_append hprefix tailTrace_1894323
  have hstable : (prefixWord ++ tailWord_1894323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894323).length < 2 ^ (prefixWord ++ tailWord_1894323).sum := by decide
  have hdescent : baseEnd_1894323 < baseStart_1894323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894330 : List Nat := [3, 1, 1, 1, 2, 1, 2, 7, 1, 4]
def baseStart_1894330 : Nat := 118140960795 + 1894330 * 2 ^ 59
def prefixEnd_1894330 : Nat := 4983230072969 + 3 ^ 40 * 1894330 * 2
def baseEnd_1894330 : Nat := 324233936077226219621047

theorem tailTrace_1894330 : CollatzResearch.WordTrace tailWord_1894330 prefixEnd_1894330 324233936077226219621047 := by
  unfold tailWord_1894330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17272972806793352662976111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46061260818115607101269629 17272972806793352662976111)
  ·
    refine ⟨25909459210190028994464167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17272972806793352662976111 25909459210190028994464167)
    ·
      refine ⟨38864188815285043491696251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25909459210190028994464167 38864188815285043491696251)
      ·
        refine ⟨58296283222927565237544377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38864188815285043491696251 58296283222927565237544377)
        ·
          refine ⟨43722212417195673928158283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58296283222927565237544377 43722212417195673928158283)
          ·
            refine ⟨65583318625793510892237425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43722212417195673928158283 65583318625793510892237425)
            ·
              refine ⟨49187488969345133169178069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65583318625793510892237425 49187488969345133169178069)
              ·
                refine ⟨1152831772719026558652611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 49187488969345133169178069 1152831772719026558652611)
                ·
                  refine ⟨1729247659078539837978917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152831772719026558652611 1729247659078539837978917)
                  ·
                    refine ⟨324233936077226219621047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729247659078539837978917 324233936077226219621047)
                    ·
                      rfl

theorem cell23_1894330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 7, 1, 4].length) (baseStart_1894330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894330 prefixEnd_1894330 := by exact prefixLift 1894330
  have htrace : WordTrace (prefixWord ++ tailWord_1894330) baseStart_1894330 baseEnd_1894330 := by
    simpa [prefixWord, tailWord_1894330, baseEnd_1894330] using wordTrace_append hprefix tailTrace_1894330
  have hstable : (prefixWord ++ tailWord_1894330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894330).length < 2 ^ (prefixWord ++ tailWord_1894330).sum := by decide
  have hdescent : baseEnd_1894330 < baseStart_1894330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894346 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_1894346 : Nat := 118140960795 + 1894346 * 2 ^ 59
def prefixEnd_1894346 : Nat := 4983230072969 + 3 ^ 40 * 1894346 * 2
def baseEnd_1894346 : Nat := 972710023922150596263067

theorem tailTrace_1894346 : CollatzResearch.WordTrace tailWord_1894346 prefixEnd_1894346 972710023922150596263067 := by
  unfold tailWord_1894346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17273118698778861346121723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46061649863410296922991261 17273118698778861346121723)
  ·
    refine ⟨25909678048168292019182585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17273118698778861346121723 25909678048168292019182585)
    ·
      refine ⟨19432258536126219014386939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25909678048168292019182585 19432258536126219014386939)
      ·
        refine ⟨29148387804189328521580409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19432258536126219014386939 29148387804189328521580409)
        ·
          refine ⟨21861290853141996391185307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29148387804189328521580409 21861290853141996391185307)
          ·
            refine ⟨32791936279712994586777961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21861290853141996391185307 32791936279712994586777961)
            ·
              refine ⟨24593952209784745940083471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32791936279712994586777961 24593952209784745940083471)
              ·
                refine ⟨36890928314677118910125207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24593952209784745940083471 36890928314677118910125207)
                ·
                  refine ⟨55336392472015678365187811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36890928314677118910125207 55336392472015678365187811)
                  ·
                    refine ⟨83004588708023517547781717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 55336392472015678365187811 83004588708023517547781717)
                    ·
                      refine ⟨972710023922150596263067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 83004588708023517547781717 972710023922150596263067)
                      ·
                        rfl

theorem cell23_1894346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_1894346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894346 prefixEnd_1894346 := by exact prefixLift 1894346
  have htrace : WordTrace (prefixWord ++ tailWord_1894346) baseStart_1894346 baseEnd_1894346 := by
    simpa [prefixWord, tailWord_1894346, baseEnd_1894346] using wordTrace_append hprefix tailTrace_1894346
  have hstable : (prefixWord ++ tailWord_1894346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894346).length < 2 ^ (prefixWord ++ tailWord_1894346).sum := by decide
  have hdescent : baseEnd_1894346 < baseStart_1894346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894347 : List Nat := [1, 1, 1, 1, 3, 4, 5, 2, 1, 4]
def baseStart_1894347 : Nat := 118140960795 + 1894347 * 2 ^ 59
def prefixEnd_1894347 : Nat := 4983230072969 + 3 ^ 40 * 1894347 * 2
def baseEnd_1894347 : Nat := 324236845800935030783521

theorem tailTrace_1894347 : CollatzResearch.WordTrace tailWord_1894347 prefixEnd_1894347 324236845800935030783521 := by
  unfold tailWord_1894347
  simp only [CollatzResearch.WordTrace]
  refine ⟨69092511268111822555273295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46061674178741215036848863 69092511268111822555273295)
  ·
    refine ⟨103638766902167733832909943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69092511268111822555273295 103638766902167733832909943)
    ·
      refine ⟨155458150353251600749364915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103638766902167733832909943 155458150353251600749364915)
      ·
        refine ⟨233187225529877401124047373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155458150353251600749364915 233187225529877401124047373)
        ·
          refine ⟨87445209573704025421517765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 233187225529877401124047373 87445209573704025421517765)
          ·
            refine ⟨16395976795069504766534581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 87445209573704025421517765 16395976795069504766534581)
            ·
              refine ⟨1537122824537766071862617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16395976795069504766534581 1537122824537766071862617)
              ·
                refine ⟨1152842118403324553896963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537122824537766071862617 1152842118403324553896963)
                ·
                  refine ⟨1729263177604986830845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1152842118403324553896963 1729263177604986830845445)
                  ·
                    refine ⟨324236845800935030783521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729263177604986830845445 324236845800935030783521)
                    ·
                      rfl

theorem cell23_1894347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 2, 1, 4].length) (baseStart_1894347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894347 prefixEnd_1894347 := by exact prefixLift 1894347
  have htrace : WordTrace (prefixWord ++ tailWord_1894347) baseStart_1894347 baseEnd_1894347 := by
    simpa [prefixWord, tailWord_1894347, baseEnd_1894347] using wordTrace_append hprefix tailTrace_1894347
  have hstable : (prefixWord ++ tailWord_1894347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894347).length < 2 ^ (prefixWord ++ tailWord_1894347).sum := by decide
  have hdescent : baseEnd_1894347 < baseStart_1894347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894403 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 4, 4]
def baseStart_1894403 : Nat := 118140960795 + 1894403 * 2 ^ 59
def prefixEnd_1894403 : Nat := 4983230072969 + 3 ^ 40 * 1894403 * 2
def baseEnd_1894403 : Nat := 324246430773152291083435

theorem tailTrace_1894403 : CollatzResearch.WordTrace tailWord_1894403 prefixEnd_1894403 324246430773152291083435 := by
  unfold tailWord_1894403
  simp only [CollatzResearch.WordTrace]
  refine ⟨69094553755908944119311863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46063035837272629412874575 69094553755908944119311863)
  ·
    refine ⟨103641830633863416178967795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69094553755908944119311863 103641830633863416178967795)
    ·
      refine ⟨155462745950795124268451693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103641830633863416178967795 155462745950795124268451693)
      ·
        refine ⟨58298529731548171600669385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155462745950795124268451693 58298529731548171600669385)
        ·
          refine ⟨43723897298661128700502039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58298529731548171600669385 43723897298661128700502039)
          ·
            refine ⟨65585845947991693050753059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43723897298661128700502039 65585845947991693050753059)
            ·
              refine ⟨98378768921987539576129589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65585845947991693050753059 98378768921987539576129589)
              ·
                refine ⟨9223009586436331835262149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98378768921987539576129589 9223009586436331835262149)
                ·
                  refine ⟨1729314297456812219111653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9223009586436331835262149 1729314297456812219111653)
                  ·
                    refine ⟨324246430773152291083435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729314297456812219111653 324246430773152291083435)
                    ·
                      rfl

theorem cell23_1894403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 4, 4].length) (baseStart_1894403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894403 prefixEnd_1894403 := by exact prefixLift 1894403
  have htrace : WordTrace (prefixWord ++ tailWord_1894403) baseStart_1894403 baseEnd_1894403 := by
    simpa [prefixWord, tailWord_1894403, baseEnd_1894403] using wordTrace_append hprefix tailTrace_1894403
  have hstable : (prefixWord ++ tailWord_1894403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894403).length < 2 ^ (prefixWord ++ tailWord_1894403).sum := by decide
  have hdescent : baseEnd_1894403 < baseStart_1894403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894443 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 3]
def baseStart_1894443 : Nat := 118140960795 + 1894443 * 2 ^ 59
def prefixEnd_1894443 : Nat := 4983230072969 + 3 ^ 40 * 1894443 * 2
def baseEnd_1894443 : Nat := 972759831545636716750121

theorem tailTrace_1894443 : CollatzResearch.WordTrace tailWord_1894443 prefixEnd_1894443 972759831545636716750121 := by
  unfold tailWord_1894443
  simp only [CollatzResearch.WordTrace]
  refine ⟨69096012675764030950767983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46064008450509353967178655 69096012675764030950767983)
  ·
    refine ⟨103644019013646046426151975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69096012675764030950767983 103644019013646046426151975)
    ·
      refine ⟨155466028520469069639227963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103644019013646046426151975 155466028520469069639227963)
      ·
        refine ⟨233199042780703604458841945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155466028520469069639227963 233199042780703604458841945)
        ·
          refine ⟨174899282085527703344131459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233199042780703604458841945 174899282085527703344131459)
          ·
            refine ⟨262348923128291555016197189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174899282085527703344131459 262348923128291555016197189)
            ·
              refine ⟨49190423086554666565536973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262348923128291555016197189 49190423086554666565536973)
              ·
                refine ⟨18446408657457999962076365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49190423086554666565536973 18446408657457999962076365)
                ·
                  refine ⟨6917403246546749985778637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18446408657457999962076365 6917403246546749985778637)
                  ·
                    refine ⟨2594026217455031244666989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6917403246546749985778637 2594026217455031244666989)
                    ·
                      refine ⟨972759831545636716750121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594026217455031244666989 972759831545636716750121)
                      ·
                        rfl

theorem cell23_1894443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 3, 3].length) (baseStart_1894443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894443 prefixEnd_1894443 := by exact prefixLift 1894443
  have htrace : WordTrace (prefixWord ++ tailWord_1894443) baseStart_1894443 baseEnd_1894443 := by
    simpa [prefixWord, tailWord_1894443, baseEnd_1894443] using wordTrace_append hprefix tailTrace_1894443
  have hstable : (prefixWord ++ tailWord_1894443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894443).length < 2 ^ (prefixWord ++ tailWord_1894443).sum := by decide
  have hdescent : baseEnd_1894443 < baseStart_1894443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894487 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 1, 3, 2]
def baseStart_1894487 : Nat := 118140960795 + 1894487 * 2 ^ 59
def prefixEnd_1894487 : Nat := 4983230072969 + 3 ^ 40 * 1894487 * 2
def baseEnd_1894487 : Nat := 972782424694434544599919

theorem tailTrace_1894487 : CollatzResearch.WordTrace tailWord_1894487 prefixEnd_1894487 972782424694434544599919 := by
  unfold tailWord_1894487
  simp only [CollatzResearch.WordTrace]
  refine ⟨69097617487604626465369715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46065078325069750976913143 69097617487604626465369715)
  ·
    refine ⟨103646426231406939698054573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69097617487604626465369715 103646426231406939698054573)
    ·
      refine ⟨38867409836777602386770465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103646426231406939698054573 38867409836777602386770465)
      ·
        refine ⟨29150557377583201790077849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38867409836777602386770465 29150557377583201790077849)
        ·
          refine ⟨21862918033187401342558387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29150557377583201790077849 21862918033187401342558387)
          ·
            refine ⟨32794377049781102013837581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21862918033187401342558387 32794377049781102013837581)
            ·
              refine ⟨12297891393667913255189093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32794377049781102013837581 12297891393667913255189093)
              ·
                refine ⟨2305854636312733735347955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12297891393667913255189093 2305854636312733735347955)
                ·
                  refine ⟨3458781954469100603021933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2305854636312733735347955 3458781954469100603021933)
                  ·
                    refine ⟨1297043232925912726133225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3458781954469100603021933 1297043232925912726133225)
                    ·
                      refine ⟨972782424694434544599919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297043232925912726133225 972782424694434544599919)
                      ·
                        rfl

theorem cell23_1894487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 3, 2].length) (baseStart_1894487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894487 prefixEnd_1894487 := by exact prefixLift 1894487
  have htrace : WordTrace (prefixWord ++ tailWord_1894487) baseStart_1894487 baseEnd_1894487 := by
    simpa [prefixWord, tailWord_1894487, baseEnd_1894487] using wordTrace_append hprefix tailTrace_1894487
  have hstable : (prefixWord ++ tailWord_1894487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894487).length < 2 ^ (prefixWord ++ tailWord_1894487).sum := by decide
  have hdescent : baseEnd_1894487 < baseStart_1894487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894553 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 1, 7]
def baseStart_1894553 : Nat := 118140960795 + 1894553 * 2 ^ 59
def prefixEnd_1894553 : Nat := 4983230072969 + 3 ^ 40 * 1894553 * 2
def baseEnd_1894553 : Nat := 324272104805877095458205

theorem tailTrace_1894553 : CollatzResearch.WordTrace tailWord_1894553 prefixEnd_1894553 324272104805877095458205 := by
  unfold tailWord_1894553
  simp only [CollatzResearch.WordTrace]
  refine ⟨69100024705365519737272313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46066683136910346491514875 69100024705365519737272313)
  ·
    refine ⟨51825018529024139802954235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69100024705365519737272313 51825018529024139802954235)
    ·
      refine ⟨77737527793536209704431353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51825018529024139802954235 77737527793536209704431353)
      ·
        refine ⟨58303145845152157278323515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77737527793536209704431353 58303145845152157278323515)
        ·
          refine ⟨87454718767728235917485273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58303145845152157278323515 87454718767728235917485273)
          ·
            refine ⟨65591039075796176938113955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87454718767728235917485273 65591039075796176938113955)
            ·
              refine ⟨98386558613694265407170933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65591039075796176938113955 98386558613694265407170933)
              ·
                refine ⟨9223739870033837381922275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98386558613694265407170933 9223739870033837381922275)
                ·
                  refine ⟨13835609805050756072883413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9223739870033837381922275 13835609805050756072883413)
                  ·
                    refine ⟨324272104805877095458205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13835609805050756072883413 324272104805877095458205)
                    ·
                      rfl

theorem cell23_1894553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 7].length) (baseStart_1894553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894553 prefixEnd_1894553 := by exact prefixLift 1894553
  have htrace : WordTrace (prefixWord ++ tailWord_1894553) baseStart_1894553 baseEnd_1894553 := by
    simpa [prefixWord, tailWord_1894553, baseEnd_1894553] using wordTrace_append hprefix tailTrace_1894553
  have hstable : (prefixWord ++ tailWord_1894553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894553).length < 2 ^ (prefixWord ++ tailWord_1894553).sum := by decide
  have hdescent : baseEnd_1894553 < baseStart_1894553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894634 : List Nat := [3, 1, 3, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1894634 : Nat := 118140960795 + 1894634 * 2 ^ 59
def prefixEnd_1894634 : Nat := 4983230072969 + 3 ^ 40 * 1894634 * 2
def baseEnd_1894634 : Nat := 324285968783548489820581

theorem tailTrace_1894634 : CollatzResearch.WordTrace tailWord_1894634 prefixEnd_1894634 324285968783548489820581 := by
  unfold tailWord_1894634
  simp only [CollatzResearch.WordTrace]
  refine ⟨17275744754518017642742739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46068652678714713713980637 17275744754518017642742739)
  ·
    refine ⟨25913617131777026464114109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17275744754518017642742739 25913617131777026464114109)
    ·
      refine ⟨9717606424416384924042791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25913617131777026464114109 9717606424416384924042791)
      ·
        refine ⟨14576409636624577386064187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9717606424416384924042791 14576409636624577386064187)
        ·
          refine ⟨21864614454936866079096281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14576409636624577386064187 21864614454936866079096281)
          ·
            refine ⟨16398460841202649559322211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21864614454936866079096281 16398460841202649559322211)
            ·
              refine ⟨24597691261803974338983317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16398460841202649559322211 24597691261803974338983317)
              ·
                refine ⟨1153016777897061297139843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24597691261803974338983317 1153016777897061297139843)
                ·
                  refine ⟨1729525166845591945709765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153016777897061297139843 1729525166845591945709765)
                  ·
                    refine ⟨324285968783548489820581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729525166845591945709765 324285968783548489820581)
                    ·
                      rfl

theorem cell23_1894634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1894634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894634 prefixEnd_1894634 := by exact prefixLift 1894634
  have htrace : WordTrace (prefixWord ++ tailWord_1894634) baseStart_1894634 baseEnd_1894634 := by
    simpa [prefixWord, tailWord_1894634, baseEnd_1894634] using wordTrace_append hprefix tailTrace_1894634
  have hstable : (prefixWord ++ tailWord_1894634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894634).length < 2 ^ (prefixWord ++ tailWord_1894634).sum := by decide
  have hdescent : baseEnd_1894634 < baseStart_1894634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894667 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 1, 5, 2]
def baseStart_1894667 : Nat := 118140960795 + 1894667 * 2 ^ 59
def prefixEnd_1894667 : Nat := 4983230072969 + 3 ^ 40 * 1894667 * 2
def baseEnd_1894667 : Nat := 972874851212243840349091

theorem tailTrace_1894667 : CollatzResearch.WordTrace tailWord_1894667 prefixEnd_1894667 972874851212243840349091 := by
  unfold tailWord_1894667
  simp only [CollatzResearch.WordTrace]
  refine ⟨69104182626952517206922255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46069455084635011471281503 69104182626952517206922255)
  ·
    refine ⟨103656273940428775810383383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69104182626952517206922255 103656273940428775810383383)
    ·
      refine ⟨155484410910643163715575075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103656273940428775810383383 155484410910643163715575075)
      ·
        refine ⟨233226616365964745573362613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155484410910643163715575075 233226616365964745573362613)
        ·
          refine ⟨21864995284309194897502745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233226616365964745573362613 21864995284309194897502745)
          ·
            refine ⟨16398746463231896173127059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21864995284309194897502745 16398746463231896173127059)
            ·
              refine ⟨24598119694847844259690589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16398746463231896173127059 24598119694847844259690589)
              ·
                refine ⟨9224294885567941597383971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24598119694847844259690589 9224294885567941597383971)
                ·
                  refine ⟨13836442328351912396075957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9224294885567941597383971 13836442328351912396075957)
                  ·
                    refine ⟨1297166468282991787132121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13836442328351912396075957 1297166468282991787132121)
                    ·
                      refine ⟨972874851212243840349091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297166468282991787132121 972874851212243840349091)
                      ·
                        rfl

theorem cell23_1894667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 5, 2].length) (baseStart_1894667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894667 prefixEnd_1894667 := by exact prefixLift 1894667
  have htrace : WordTrace (prefixWord ++ tailWord_1894667) baseStart_1894667 baseEnd_1894667 := by
    simpa [prefixWord, tailWord_1894667, baseEnd_1894667] using wordTrace_append hprefix tailTrace_1894667
  have hstable : (prefixWord ++ tailWord_1894667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894667).length < 2 ^ (prefixWord ++ tailWord_1894667).sum := by decide
  have hdescent : baseEnd_1894667 < baseStart_1894667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894677 : List Nat := [1, 3, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_1894677 : Nat := 118140960795 + 1894677 * 2 ^ 59
def prefixEnd_1894677 : Nat := 4983230072969 + 3 ^ 40 * 1894677 * 2
def baseEnd_1894677 : Nat := 324293328672929600408015

theorem tailTrace_1894677 : CollatzResearch.WordTrace tailWord_1894677 prefixEnd_1894677 324293328672929600408015 := by
  unfold tailWord_1894677
  simp only [CollatzResearch.WordTrace]
  refine ⟨69104547356916288914786285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46069698237944192609857523 69104547356916288914786285)
  ·
    refine ⟨25914205258843608343044857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69104547356916288914786285 25914205258843608343044857)
    ·
      refine ⟨19435653944132706257283643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25914205258843608343044857 19435653944132706257283643)
      ·
        refine ⟨29153480916199059385925465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19435653944132706257283643 29153480916199059385925465)
        ·
          refine ⟨21865110687149294539444099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29153480916199059385925465 21865110687149294539444099)
          ·
            refine ⟨32797666030723941809166149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21865110687149294539444099 32797666030723941809166149)
            ·
              refine ⟨6149562380760739089218653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32797666030723941809166149 6149562380760739089218653)
              ·
                refine ⟨2306085892785277158456995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6149562380760739089218653 2306085892785277158456995)
                ·
                  refine ⟨3459128839177915737685493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306085892785277158456995 3459128839177915737685493)
                  ·
                    refine ⟨324293328672929600408015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3459128839177915737685493 324293328672929600408015)
                    ·
                      rfl

theorem cell23_1894677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_1894677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894677 prefixEnd_1894677 := by exact prefixLift 1894677
  have htrace : WordTrace (prefixWord ++ tailWord_1894677) baseStart_1894677 baseEnd_1894677 := by
    simpa [prefixWord, tailWord_1894677, baseEnd_1894677] using wordTrace_append hprefix tailTrace_1894677
  have hstable : (prefixWord ++ tailWord_1894677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894677).length < 2 ^ (prefixWord ++ tailWord_1894677).sum := by decide
  have hdescent : baseEnd_1894677 < baseStart_1894677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894698 : List Nat := [3, 1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_1894698 : Nat := 118140960795 + 1894698 * 2 ^ 59
def prefixEnd_1894698 : Nat := 4983230072969 + 3 ^ 40 * 1894698 * 2
def baseEnd_1894698 : Nat := 108098974345837024340161

theorem tailTrace_1894698 : CollatzResearch.WordTrace tailWord_1894698 prefixEnd_1894698 108098974345837024340161 := by
  unfold tailWord_1894698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17276328322460052375325187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46070208859893473000867165 17276328322460052375325187)
  ·
    refine ⟨25914492483690078562987781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17276328322460052375325187 25914492483690078562987781)
    ·
      refine ⟨4858967340691889730560209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25914492483690078562987781 4858967340691889730560209)
      ·
        refine ⟨3644225505518917297920157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4858967340691889730560209 3644225505518917297920157)
        ·
          refine ⟨1366584564569593986720059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3644225505518917297920157 1366584564569593986720059)
          ·
            refine ⟨2049876846854390980080089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1366584564569593986720059 2049876846854390980080089)
            ·
              refine ⟨1537407635140793235060067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2049876846854390980080089 1537407635140793235060067)
              ·
                refine ⟨2306111452711189852590101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537407635140793235060067 2306111452711189852590101)
                ·
                  refine ⟨108098974345837024340161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2306111452711189852590101 108098974345837024340161)
                  ·
                    rfl

theorem cell23_1894698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_1894698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894698 prefixEnd_1894698 := by exact prefixLift 1894698
  have htrace : WordTrace (prefixWord ++ tailWord_1894698) baseStart_1894698 baseEnd_1894698 := by
    simpa [prefixWord, tailWord_1894698, baseEnd_1894698] using wordTrace_append hprefix tailTrace_1894698
  have hstable : (prefixWord ++ tailWord_1894698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894698).length < 2 ^ (prefixWord ++ tailWord_1894698).sum := by decide
  have hdescent : baseEnd_1894698 < baseStart_1894698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894714 : List Nat := [3, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4]
def baseStart_1894714 : Nat := 118140960795 + 1894714 * 2 ^ 59
def prefixEnd_1894714 : Nat := 4983230072969 + 3 ^ 40 * 1894714 * 2
def baseEnd_1894714 : Nat := 972898984803005156461375

theorem tailTrace_1894714 : CollatzResearch.WordTrace tailWord_1894714 prefixEnd_1894714 972898984803005156461375 := by
  unfold tailWord_1894714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17276474214445561058470799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46070597905188162822588797 17276474214445561058470799)
  ·
    refine ⟨25914711321668341587706199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17276474214445561058470799 25914711321668341587706199)
    ·
      refine ⟨38872066982502512381559299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25914711321668341587706199 38872066982502512381559299)
      ·
        refine ⟨58308100473753768572338949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38872066982502512381559299 58308100473753768572338949)
        ·
          refine ⟨10932768838828831607313553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58308100473753768572338949 10932768838828831607313553)
          ·
            refine ⟨8199576629121623705485165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10932768838828831607313553 8199576629121623705485165)
            ·
              refine ⟨3074841235920608889556937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8199576629121623705485165 3074841235920608889556937)
              ·
                refine ⟨2306130926940456667167703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074841235920608889556937 2306130926940456667167703)
                ·
                  refine ⟨3459196390410685000751555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306130926940456667167703 3459196390410685000751555)
                  ·
                    refine ⟨5188794585616027501127333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3459196390410685000751555 5188794585616027501127333)
                    ·
                      refine ⟨972898984803005156461375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5188794585616027501127333 972898984803005156461375)
                      ·
                        rfl

theorem cell23_1894714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4].length) (baseStart_1894714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894714 prefixEnd_1894714 := by exact prefixLift 1894714
  have htrace : WordTrace (prefixWord ++ tailWord_1894714) baseStart_1894714 baseEnd_1894714 := by
    simpa [prefixWord, tailWord_1894714, baseEnd_1894714] using wordTrace_append hprefix tailTrace_1894714
  have hstable : (prefixWord ++ tailWord_1894714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894714).length < 2 ^ (prefixWord ++ tailWord_1894714).sum := by decide
  have hdescent : baseEnd_1894714 < baseStart_1894714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894727 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1894727 : Nat := 118140960795 + 1894727 * 2 ^ 59
def prefixEnd_1894727 : Nat := 4983230072969 + 3 ^ 40 * 1894727 * 2
def baseEnd_1894727 : Nat := 972905660051513605598815

theorem tailTrace_1894727 : CollatzResearch.WordTrace tailWord_1894727 prefixEnd_1894727 972905660051513605598815 := by
  unfold tailWord_1894727
  simp only [CollatzResearch.WordTrace]
  refine ⟨69106371006735147454106435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46070914004490098302737623 69106371006735147454106435)
  ·
    refine ⟨103659556510102721181159653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69106371006735147454106435 103659556510102721181159653)
    ·
      refine ⟨19436166845644260221467435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103659556510102721181159653 19436166845644260221467435)
      ·
        refine ⟨29154250268466390332201153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19436166845644260221467435 29154250268466390332201153)
        ·
          refine ⟨21865687701349792749150865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29154250268466390332201153 21865687701349792749150865)
          ·
            refine ⟨16399265776012344561863149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21865687701349792749150865 16399265776012344561863149)
            ·
              refine ⟨6149724666004629210698681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16399265776012344561863149 6149724666004629210698681)
              ·
                refine ⟨4612293499503471908024011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6149724666004629210698681 4612293499503471908024011)
                ·
                  refine ⟨6918440249255207862036017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4612293499503471908024011 6918440249255207862036017)
                  ·
                    refine ⟨5188830186941405896527013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6918440249255207862036017 5188830186941405896527013)
                    ·
                      refine ⟨972905660051513605598815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5188830186941405896527013 972905660051513605598815)
                      ·
                        rfl

theorem cell23_1894727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1894727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894727 prefixEnd_1894727 := by exact prefixLift 1894727
  have htrace : WordTrace (prefixWord ++ tailWord_1894727) baseStart_1894727 baseEnd_1894727 := by
    simpa [prefixWord, tailWord_1894727, baseEnd_1894727] using wordTrace_append hprefix tailTrace_1894727
  have hstable : (prefixWord ++ tailWord_1894727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894727).length < 2 ^ (prefixWord ++ tailWord_1894727).sum := by decide
  have hdescent : baseEnd_1894727 < baseStart_1894727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894741 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 2, 4]
def baseStart_1894741 : Nat := 118140960795 + 1894741 * 2 ^ 59
def prefixEnd_1894741 : Nat := 4983230072969 + 3 ^ 40 * 1894741 * 2
def baseEnd_1894741 : Nat := 324304282926892183607917

theorem tailTrace_1894741 : CollatzResearch.WordTrace tailWord_1894741 prefixEnd_1894741 324304282926892183607917 := by
  unfold tailWord_1894741
  simp only [CollatzResearch.WordTrace]
  refine ⟨69106881628684427845116077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46071254419122951896744051 69106881628684427845116077)
  ·
    refine ⟨25915080610756660441918529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69106881628684427845116077 25915080610756660441918529)
    ·
      refine ⟨19436310458067495331438897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25915080610756660441918529 19436310458067495331438897)
      ·
        refine ⟨14577232843550621498579173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19436310458067495331438897 14577232843550621498579173)
        ·
          refine ⟨2733231158165741530983595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14577232843550621498579173 2733231158165741530983595)
          ·
            refine ⟨4099846737248612296475393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733231158165741530983595 4099846737248612296475393)
            ·
              refine ⟨3074885052936459222356545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4099846737248612296475393 3074885052936459222356545)
              ·
                refine ⟨2306163789702344416767409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074885052936459222356545 2306163789702344416767409)
                ·
                  refine ⟨1729622842276758312575557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306163789702344416767409 1729622842276758312575557)
                  ·
                    refine ⟨324304282926892183607917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729622842276758312575557 324304282926892183607917)
                    ·
                      rfl

theorem cell23_1894741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_1894741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894741 prefixEnd_1894741 := by exact prefixLift 1894741
  have htrace : WordTrace (prefixWord ++ tailWord_1894741) baseStart_1894741 baseEnd_1894741 := by
    simpa [prefixWord, tailWord_1894741, baseEnd_1894741] using wordTrace_append hprefix tailTrace_1894741
  have hstable : (prefixWord ++ tailWord_1894741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894741).length < 2 ^ (prefixWord ++ tailWord_1894741).sum := by decide
  have hdescent : baseEnd_1894741 < baseStart_1894741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894754 : List Nat := [3, 3, 2, 1, 1, 4, 1, 8]
def baseStart_1894754 : Nat := 118140960795 + 1894754 * 2 ^ 59
def prefixEnd_1894754 : Nat := 4983230072969 + 3 ^ 40 * 1894754 * 2
def baseEnd_1894754 : Nat := 36034056445525370368933

theorem tailTrace_1894754 : CollatzResearch.WordTrace tailWord_1894754 prefixEnd_1894754 36034056445525370368933 := by
  unfold tailWord_1894754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17276838944409332766334829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46071570518424887376892877 17276838944409332766334829)
  ·
    refine ⟨6478814604153499787375561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17276838944409332766334829 6478814604153499787375561)
    ·
      refine ⟨4859110953115124840531671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6478814604153499787375561 4859110953115124840531671)
      ·
        refine ⟨7288666429672687260797507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4859110953115124840531671 7288666429672687260797507)
        ·
          refine ⟨10932999644509030891196261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7288666429672687260797507 10932999644509030891196261)
          ·
            refine ⟨2049937433345443292099299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10932999644509030891196261 2049937433345443292099299)
            ·
              refine ⟨3074906150018164938148949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2049937433345443292099299 3074906150018164938148949)
              ·
                refine ⟨36034056445525370368933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3074906150018164938148949 36034056445525370368933)
                ·
                  rfl

theorem cell23_1894754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 8].length) (baseStart_1894754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894754 prefixEnd_1894754 := by exact prefixLift 1894754
  have htrace : WordTrace (prefixWord ++ tailWord_1894754) baseStart_1894754 baseEnd_1894754 := by
    simpa [prefixWord, tailWord_1894754, baseEnd_1894754] using wordTrace_append hprefix tailTrace_1894754
  have hstable : (prefixWord ++ tailWord_1894754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894754).length < 2 ^ (prefixWord ++ tailWord_1894754).sum := by decide
  have hdescent : baseEnd_1894754 < baseStart_1894754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894791 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 1, 3, 2]
def baseStart_1894791 : Nat := 118140960795 + 1894791 * 2 ^ 59
def prefixEnd_1894791 : Nat := 4983230072969 + 3 ^ 40 * 1894791 * 2
def baseEnd_1894791 : Nat := 972938522813401355198521

theorem tailTrace_1894791 : CollatzResearch.WordTrace tailWord_1894791 prefixEnd_1894791 972938522813401355198521 := by
  unfold tailWord_1894791
  simp only [CollatzResearch.WordTrace]
  refine ⟨69108705278503286384436227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46072470185668857589624151 69108705278503286384436227)
  ·
    refine ⟨103663057917754929576654341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69108705278503286384436227 103663057917754929576654341)
    ·
      refine ⟨19436823359579049295622689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103663057917754929576654341 19436823359579049295622689)
      ·
        refine ⟨14577617519684286971717017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19436823359579049295622689 14577617519684286971717017)
        ·
          refine ⟨10933213139763215228787763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14577617519684286971717017 10933213139763215228787763)
          ·
            refine ⟨16399819709644822843181645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10933213139763215228787763 16399819709644822843181645)
            ·
              refine ⟨6149932391116808566193117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16399819709644822843181645 6149932391116808566193117)
              ·
                refine ⟨2306224646668803212322419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6149932391116808566193117 2306224646668803212322419)
                ·
                  refine ⟨3459336970003204818483629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306224646668803212322419 3459336970003204818483629)
                  ·
                    refine ⟨1297251363751201806931361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3459336970003204818483629 1297251363751201806931361)
                    ·
                      refine ⟨972938522813401355198521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297251363751201806931361 972938522813401355198521)
                      ·
                        rfl

theorem cell23_1894791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_1894791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894791 prefixEnd_1894791 := by exact prefixLift 1894791
  have htrace : WordTrace (prefixWord ++ tailWord_1894791) baseStart_1894791 baseEnd_1894791 := by
    simpa [prefixWord, tailWord_1894791, baseEnd_1894791] using wordTrace_append hprefix tailTrace_1894791
  have hstable : (prefixWord ++ tailWord_1894791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894791).length < 2 ^ (prefixWord ++ tailWord_1894791).sum := by decide
  have hdescent : baseEnd_1894791 < baseStart_1894791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894798 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_1894798 : Nat := 118140960795 + 1894798 * 2 ^ 59
def prefixEnd_1894798 : Nat := 4983230072969 + 3 ^ 40 * 1894798 * 2
def baseEnd_1894798 : Nat := 972942117177982827810989

theorem tailTrace_1894798 : CollatzResearch.WordTrace tailWord_1894798 prefixEnd_1894798 972942117177982827810989 := by
  unfold tailWord_1894798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8638620073684740822492631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46072640392985284386627365 8638620073684740822492631)
  ·
    refine ⟨12957930110527111233738947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8638620073684740822492631 12957930110527111233738947)
    ·
      refine ⟨19436895165790666850608421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12957930110527111233738947 19436895165790666850608421)
      ·
        refine ⟨3644417843585750034489079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19436895165790666850608421 3644417843585750034489079)
        ·
          refine ⟨5466626765378625051733619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644417843585750034489079 5466626765378625051733619)
          ·
            refine ⟨8199940148067937577600429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5466626765378625051733619 8199940148067937577600429)
            ·
              refine ⟨3074977555525476591600161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8199940148067937577600429 3074977555525476591600161)
              ·
                refine ⟨2306233166644107443700121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3074977555525476591600161 2306233166644107443700121)
                ·
                  refine ⟨1729674874983080582775091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306233166644107443700121 1729674874983080582775091)
                  ·
                    refine ⟨2594512312474620874162637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1729674874983080582775091 2594512312474620874162637)
                    ·
                      refine ⟨972942117177982827810989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594512312474620874162637 972942117177982827810989)
                      ·
                        rfl

theorem cell23_1894798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_1894798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894798 prefixEnd_1894798 := by exact prefixLift 1894798
  have htrace : WordTrace (prefixWord ++ tailWord_1894798) baseStart_1894798 baseEnd_1894798 := by
    simpa [prefixWord, tailWord_1894798, baseEnd_1894798] using wordTrace_append hprefix tailTrace_1894798
  have hstable : (prefixWord ++ tailWord_1894798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894798).length < 2 ^ (prefixWord ++ tailWord_1894798).sum := by decide
  have hdescent : baseEnd_1894798 < baseStart_1894798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894807 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 3]
def baseStart_1894807 : Nat := 118140960795 + 1894807 * 2 ^ 59
def prefixEnd_1894807 : Nat := 4983230072969 + 3 ^ 40 * 1894807 * 2
def baseEnd_1894807 : Nat := 972946738503873292598447

theorem tailTrace_1894807 : CollatzResearch.WordTrace tailWord_1894807 prefixEnd_1894807 972946738503873292598447 := by
  unfold tailWord_1894807
  simp only [CollatzResearch.WordTrace]
  refine ⟨69109288846445321117018675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46072859230963547411345783 69109288846445321117018675)
  ·
    refine ⟨103663933269667981675528013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69109288846445321117018675 103663933269667981675528013)
    ·
      refine ⟨38873974976125493128323005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103663933269667981675528013 38873974976125493128323005)
      ·
        refine ⟨14577740616047059923121127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38873974976125493128323005 14577740616047059923121127)
        ·
          refine ⟨21866610924070589884681691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14577740616047059923121127 21866610924070589884681691)
          ·
            refine ⟨32799916386105884827022537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21866610924070589884681691 32799916386105884827022537)
            ·
              refine ⟨24599937289579413620266903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32799916386105884827022537 24599937289579413620266903)
              ·
                refine ⟨36899905934369120430400355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24599937289579413620266903 36899905934369120430400355)
                ·
                  refine ⟨55349858901553680645600533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36899905934369120430400355 55349858901553680645600533)
                  ·
                    refine ⟨2594524636010328780262525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55349858901553680645600533 2594524636010328780262525)
                    ·
                      refine ⟨972946738503873292598447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594524636010328780262525 972946738503873292598447)
                      ·
                        rfl

theorem cell23_1894807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_1894807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894807 prefixEnd_1894807 := by exact prefixLift 1894807
  have htrace : WordTrace (prefixWord ++ tailWord_1894807) baseStart_1894807 baseEnd_1894807 := by
    simpa [prefixWord, tailWord_1894807, baseEnd_1894807] using wordTrace_append hprefix tailTrace_1894807
  have hstable : (prefixWord ++ tailWord_1894807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894807).length < 2 ^ (prefixWord ++ tailWord_1894807).sum := by decide
  have hdescent : baseEnd_1894807 < baseStart_1894807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894857 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 4, 5]
def baseStart_1894857 : Nat := 118140960795 + 1894857 * 2 ^ 59
def prefixEnd_1894857 : Nat := 4983230072969 + 3 ^ 40 * 1894857 * 2
def baseEnd_1894857 : Nat := 324324137512199365657739

theorem tailTrace_1894857 : CollatzResearch.WordTrace tailWord_1894857 prefixEnd_1894857 324324137512199365657739 := by
  unfold tailWord_1894857
  simp only [CollatzResearch.WordTrace]
  refine ⟨69111112496264179656338825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46074074997509453104225883 69111112496264179656338825)
  ·
    refine ⟨51833334372198134742254119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69111112496264179656338825 51833334372198134742254119)
    ·
      refine ⟨77750001558297202113381179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51833334372198134742254119 77750001558297202113381179)
      ·
        refine ⟨116625002337445803170071769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77750001558297202113381179 116625002337445803170071769)
        ·
          refine ⟨87468751753084352377553827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116625002337445803170071769 87468751753084352377553827)
          ·
            refine ⟨131203127629626528566330741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87468751753084352377553827 131203127629626528566330741)
            ·
              refine ⟨12300293215277487053093507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131203127629626528566330741 12300293215277487053093507)
              ·
                refine ⟨18450439822916230579640261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12300293215277487053093507 18450439822916230579640261)
                ·
                  refine ⟨3459457466796793233682549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18450439822916230579640261 3459457466796793233682549)
                  ·
                    refine ⟨324324137512199365657739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3459457466796793233682549 324324137512199365657739)
                    ·
                      rfl

theorem cell23_1894857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 5].length) (baseStart_1894857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894857 prefixEnd_1894857 := by exact prefixLift 1894857
  have htrace : WordTrace (prefixWord ++ tailWord_1894857) baseStart_1894857 baseEnd_1894857 := by
    simpa [prefixWord, tailWord_1894857, baseEnd_1894857] using wordTrace_append hprefix tailTrace_1894857
  have hstable : (prefixWord ++ tailWord_1894857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894857).length < 2 ^ (prefixWord ++ tailWord_1894857).sum := by decide
  have hdescent : baseEnd_1894857 < baseStart_1894857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894917 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 8]
def baseStart_1894917 : Nat := 118140960795 + 1894917 * 2 ^ 59
def prefixEnd_1894917 : Nat := 4983230072969 + 3 ^ 40 * 1894917 * 2
def baseEnd_1894917 : Nat := 108111469041763095802549

theorem tailTrace_1894917 : CollatzResearch.WordTrace tailWord_1894917 prefixEnd_1894917 108111469041763095802549 := by
  unfold tailWord_1894917
  simp only [CollatzResearch.WordTrace]
  refine ⟨69113300876046809903523005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46075533917364539935682003 69113300876046809903523005)
  ·
    refine ⟨25917487828517553713821127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69113300876046809903523005 25917487828517553713821127)
    ·
      refine ⟨38876231742776330570731691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25917487828517553713821127 38876231742776330570731691)
      ·
        refine ⟨58314347614164495856097537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38876231742776330570731691 58314347614164495856097537)
        ·
          refine ⟨43735760710623371892073153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58314347614164495856097537 43735760710623371892073153)
          ·
            refine ⟨32801820532967528919054865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43735760710623371892073153 32801820532967528919054865)
            ·
              refine ⟨24601365399725646689291149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32801820532967528919054865 24601365399725646689291149)
              ·
                refine ⟨9225512024897117508484181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24601365399725646689291149 9225512024897117508484181)
                ·
                  refine ⟨108111469041763095802549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9225512024897117508484181 108111469041763095802549)
                  ·
                    rfl

theorem cell23_1894917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_1894917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894917 prefixEnd_1894917 := by exact prefixLift 1894917
  have htrace : WordTrace (prefixWord ++ tailWord_1894917) baseStart_1894917 baseEnd_1894917 := by
    simpa [prefixWord, tailWord_1894917, baseEnd_1894917] using wordTrace_append hprefix tailTrace_1894917
  have hstable : (prefixWord ++ tailWord_1894917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894917).length < 2 ^ (prefixWord ++ tailWord_1894917).sum := by decide
  have hdescent : baseEnd_1894917 < baseStart_1894917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894937 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_1894937 : Nat := 118140960795 + 1894937 * 2 ^ 59
def prefixEnd_1894937 : Nat := 4983230072969 + 3 ^ 40 * 1894937 * 2
def baseEnd_1894937 : Nat := 973013490988957783972849

theorem tailTrace_1894937 : CollatzResearch.WordTrace tailWord_1894937 prefixEnd_1894937 973013490988957783972849 := by
  unfold tailWord_1894937
  simp only [CollatzResearch.WordTrace]
  refine ⟨69114030335974353319251065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46076020223982902212834043 69114030335974353319251065)
  ·
    refine ⟨51835522751980764989438299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69114030335974353319251065 51835522751980764989438299)
    ·
      refine ⟨77753284127971147484157449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51835522751980764989438299 77753284127971147484157449)
      ·
        refine ⟨58314963095978360613118087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77753284127971147484157449 58314963095978360613118087)
        ·
          refine ⟨87472444643967540919677131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58314963095978360613118087 87472444643967540919677131)
          ·
            refine ⟨131208666965951311379515697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87472444643967540919677131 131208666965951311379515697)
            ·
              refine ⟨98406500224463483534636773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131208666965951311379515697 98406500224463483534636773)
              ·
                refine ⟨18451218792086903162744395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 98406500224463483534636773 18451218792086903162744395)
                ·
                  refine ⟨27676828188130354744116593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18451218792086903162744395 27676828188130354744116593)
                  ·
                    refine ⟨20757621141097766058087445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27676828188130354744116593 20757621141097766058087445)
                    ·
                      refine ⟨973013490988957783972849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20757621141097766058087445 973013490988957783972849)
                      ·
                        rfl

theorem cell23_1894937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_1894937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894937 prefixEnd_1894937 := by exact prefixLift 1894937
  have htrace : WordTrace (prefixWord ++ tailWord_1894937) baseStart_1894937 baseEnd_1894937 := by
    simpa [prefixWord, tailWord_1894937, baseEnd_1894937] using wordTrace_append hprefix tailTrace_1894937
  have hstable : (prefixWord ++ tailWord_1894937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894937).length < 2 ^ (prefixWord ++ tailWord_1894937).sum := by decide
  have hdescent : baseEnd_1894937 < baseStart_1894937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894948 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1894948 : Nat := 118140960795 + 1894948 * 2 ^ 59
def prefixEnd_1894948 : Nat := 4983230072969 + 3 ^ 40 * 1894948 * 2
def baseEnd_1894948 : Nat := 973019139276157240935299

theorem tailTrace_1894948 : CollatzResearch.WordTrace tailWord_1894948 prefixEnd_1894948 973019139276157240935299 := by
  unfold tailWord_1894948
  simp only [CollatzResearch.WordTrace]
  refine ⟨34557215769467251098950749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46076287692623001465267665 34557215769467251098950749)
  ·
    refine ⟨12958955913550219162106531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34557215769467251098950749 12958955913550219162106531)
    ·
      refine ⟨19438433870325328743159797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12958955913550219162106531 19438433870325328743159797)
      ·
        refine ⟨1822353175342999569671231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19438433870325328743159797 1822353175342999569671231)
        ·
          refine ⟨2733529763014499354506847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822353175342999569671231 2733529763014499354506847)
          ·
            refine ⟨4100294644521749031760271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733529763014499354506847 4100294644521749031760271)
            ·
              refine ⟨6150441966782623547640407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100294644521749031760271 6150441966782623547640407)
              ·
                refine ⟨9225662950173935321460611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150441966782623547640407 9225662950173935321460611)
                ·
                  refine ⟨13838494425260902982190917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9225662950173935321460611 13838494425260902982190917)
                  ·
                    refine ⟨2594717704736419309160797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13838494425260902982190917 2594717704736419309160797)
                    ·
                      refine ⟨973019139276157240935299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594717704736419309160797 973019139276157240935299)
                      ·
                        rfl

theorem cell23_1894948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1894948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894948 prefixEnd_1894948 := by exact prefixLift 1894948
  have htrace : WordTrace (prefixWord ++ tailWord_1894948) baseStart_1894948 baseEnd_1894948 := by
    simpa [prefixWord, tailWord_1894948, baseEnd_1894948] using wordTrace_append hprefix tailTrace_1894948
  have hstable : (prefixWord ++ tailWord_1894948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894948).length < 2 ^ (prefixWord ++ tailWord_1894948).sum := by decide
  have hdescent : baseEnd_1894948 < baseStart_1894948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1894984 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1894984 : Nat := 118140960795 + 1894984 * 2 ^ 59
def prefixEnd_1894984 : Nat := 4983230072969 + 3 ^ 40 * 1894984 * 2
def baseEnd_1894984 : Nat := 973037624579719100085133

theorem tailTrace_1894984 : CollatzResearch.WordTrace tailWord_1894984 prefixEnd_1894984 973037624579719100085133 := by
  unfold tailWord_1894984
  simp only [CollatzResearch.WordTrace]
  refine ⟨34557872283402040173106003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46077163044536053564141337 34557872283402040173106003)
  ·
    refine ⟨51836808425103060259659005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34557872283402040173106003 51836808425103060259659005)
    ·
      refine ⟨19438803159413647597372127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51836808425103060259659005 19438803159413647597372127)
      ·
        refine ⟨29158204739120471396058191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19438803159413647597372127 29158204739120471396058191)
        ·
          refine ⟨43737307108680707094087287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29158204739120471396058191 43737307108680707094087287)
          ·
            refine ⟨65605960663021060641130931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43737307108680707094087287 65605960663021060641130931)
            ·
              refine ⟨98408940994531590961696397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65605960663021060641130931 98408940994531590961696397)
              ·
                refine ⟨36903352872949346610636149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98408940994531590961696397 36903352872949346610636149)
                ·
                  refine ⟨3459689331839001244747139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36903352872949346610636149 3459689331839001244747139)
                  ·
                    refine ⟨5189533997758501867120709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3459689331839001244747139 5189533997758501867120709)
                    ·
                      refine ⟨973037624579719100085133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5189533997758501867120709 973037624579719100085133)
                      ·
                        rfl

theorem cell23_1894984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1894984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1894984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1894984 prefixEnd_1894984 := by exact prefixLift 1894984
  have htrace : WordTrace (prefixWord ++ tailWord_1894984) baseStart_1894984 baseEnd_1894984 := by
    simpa [prefixWord, tailWord_1894984, baseEnd_1894984] using wordTrace_append hprefix tailTrace_1894984
  have hstable : (prefixWord ++ tailWord_1894984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1894984).length < 2 ^ (prefixWord ++ tailWord_1894984).sum := by decide
  have hdescent : baseEnd_1894984 < baseStart_1894984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1894984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895006 : List Nat := [4, 4, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_1895006 : Nat := 118140960795 + 1895006 * 2 ^ 59
def prefixEnd_1895006 : Nat := 4983230072969 + 3 ^ 40 * 1895006 * 2
def baseEnd_1895006 : Nat := 324349640384706004670011

theorem tailTrace_1895006 : CollatzResearch.WordTrace tailWord_1895006 prefixEnd_1895006 324349640384706004670011 := by
  unfold tailWord_1895006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8639568371590547262939109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46077697981816252069008581 8639568371590547262939109)
  ·
    refine ⟨1619919069673227611801083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8639568371590547262939109 1619919069673227611801083)
    ·
      refine ⟨2429878604509841417701625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1619919069673227611801083 2429878604509841417701625)
      ·
        refine ⟨1822408953382381063276219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2429878604509841417701625 1822408953382381063276219)
        ·
          refine ⟨2733613430073571594914329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1822408953382381063276219 2733613430073571594914329)
          ·
            refine ⟨2050210072555178696185747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2733613430073571594914329 2050210072555178696185747)
            ·
              refine ⟨3075315108832768044278621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050210072555178696185747 3075315108832768044278621)
              ·
                refine ⟨1153243165812288016604483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3075315108832768044278621 1153243165812288016604483)
                ·
                  refine ⟨1729864748718432024906725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153243165812288016604483 1729864748718432024906725)
                  ·
                    refine ⟨324349640384706004670011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729864748718432024906725 324349640384706004670011)
                    ·
                      rfl

theorem cell23_1895006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_1895006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895006 prefixEnd_1895006 := by exact prefixLift 1895006
  have htrace : WordTrace (prefixWord ++ tailWord_1895006) baseStart_1895006 baseEnd_1895006 := by
    simpa [prefixWord, tailWord_1895006, baseEnd_1895006] using wordTrace_append hprefix tailTrace_1895006
  have hstable : (prefixWord ++ tailWord_1895006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895006).length < 2 ^ (prefixWord ++ tailWord_1895006).sum := by decide
  have hdescent : baseEnd_1895006 < baseStart_1895006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895021 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1895021 : Nat := 118140960795 + 1895021 * 2 ^ 59
def prefixEnd_1895021 : Nat := 4983230072969 + 3 ^ 40 * 1895021 * 2
def baseEnd_1895021 : Nat := 973056623363935455322463

theorem tailTrace_1895021 : CollatzResearch.WordTrace tailWord_1895021 prefixEnd_1895021 973056623363935455322463 := by
  unfold tailWord_1895021
  simp only [CollatzResearch.WordTrace]
  refine ⟨69117094067670035665308917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46078062711780023776872611 69117094067670035665308917)
  ·
    refine ⟨6479727568844065843622711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69117094067670035665308917 6479727568844065843622711)
    ·
      refine ⟨9719591353266098765434067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6479727568844065843622711 9719591353266098765434067)
      ·
        refine ⟨14579387029899148148151101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9719591353266098765434067 14579387029899148148151101)
        ·
          refine ⟨5467270136212180555556663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14579387029899148148151101 5467270136212180555556663)
          ·
            refine ⟨8200905204318270833334995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467270136212180555556663 8200905204318270833334995)
            ·
              refine ⟨12301357806477406250002493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8200905204318270833334995 12301357806477406250002493)
              ·
                refine ⟨4613009177429027343750935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12301357806477406250002493 4613009177429027343750935)
                ·
                  refine ⟨6919513766143541015626403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613009177429027343750935 6919513766143541015626403)
                  ·
                    refine ⟨10379270649215311523439605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6919513766143541015626403 10379270649215311523439605)
                    ·
                      refine ⟨973056623363935455322463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10379270649215311523439605 973056623363935455322463)
                      ·
                        rfl

theorem cell23_1895021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1895021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895021 prefixEnd_1895021 := by exact prefixLift 1895021
  have htrace : WordTrace (prefixWord ++ tailWord_1895021) baseStart_1895021 baseEnd_1895021 := by
    simpa [prefixWord, tailWord_1895021, baseEnd_1895021] using wordTrace_append hprefix tailTrace_1895021
  have hstable : (prefixWord ++ tailWord_1895021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895021).length < 2 ^ (prefixWord ++ tailWord_1895021).sum := by decide
  have hdescent : baseEnd_1895021 < baseStart_1895021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895029 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_1895029 : Nat := 118140960795 + 1895029 * 2 ^ 59
def prefixEnd_1895029 : Nat := 4983230072969 + 3 ^ 40 * 1895029 * 2
def baseEnd_1895029 : Nat := 973060731209171424022427

theorem tailTrace_1895029 : CollatzResearch.WordTrace tailWord_1895029 prefixEnd_1895029 973060731209171424022427 := by
  unfold tailWord_1895029
  simp only [CollatzResearch.WordTrace]
  refine ⟨69117385851641053031600141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46078257234427368687733427 69117385851641053031600141)
  ·
    refine ⟨25919019694365394886850053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69117385851641053031600141 25919019694365394886850053)
    ·
      refine ⟨4859816192693511541284385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25919019694365394886850053 4859816192693511541284385)
      ·
        refine ⟨3644862144520133655963289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4859816192693511541284385 3644862144520133655963289)
        ·
          refine ⟨2733646608390100241972467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3644862144520133655963289 2733646608390100241972467)
          ·
            refine ⟨4100469912585150362958701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2733646608390100241972467 4100469912585150362958701)
            ·
              refine ⟨1537676217219431386109513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4100469912585150362958701 1537676217219431386109513)
              ·
                refine ⟨1153257162914573539582135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537676217219431386109513 1153257162914573539582135)
                ·
                  refine ⟨1729885744371860309373203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153257162914573539582135 1729885744371860309373203)
                  ·
                    refine ⟨2594828616557790464059805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1729885744371860309373203 2594828616557790464059805)
                    ·
                      refine ⟨973060731209171424022427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594828616557790464059805 973060731209171424022427)
                      ·
                        rfl

theorem cell23_1895029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_1895029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895029 prefixEnd_1895029 := by exact prefixLift 1895029
  have htrace : WordTrace (prefixWord ++ tailWord_1895029) baseStart_1895029 baseEnd_1895029 := by
    simpa [prefixWord, tailWord_1895029, baseEnd_1895029] using wordTrace_append hprefix tailTrace_1895029
  have hstable : (prefixWord ++ tailWord_1895029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895029).length < 2 ^ (prefixWord ++ tailWord_1895029).sum := by decide
  have hdescent : baseEnd_1895029 < baseStart_1895029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895045 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 2, 4]
def baseStart_1895045 : Nat := 118140960795 + 1895045 * 2 ^ 59
def prefixEnd_1895045 : Nat := 4983230072969 + 3 ^ 40 * 1895045 * 2
def baseEnd_1895045 : Nat := 324356315633214453807451

theorem tailTrace_1895045 : CollatzResearch.WordTrace tailWord_1895045 prefixEnd_1895045 324356315633214453807451 := by
  unfold tailWord_1895045
  simp only [CollatzResearch.WordTrace]
  refine ⟨69117969419583087764182589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46078646279722058509455059 69117969419583087764182589)
  ·
    refine ⟨25919238532343657911568471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69117969419583087764182589 25919238532343657911568471)
    ·
      refine ⟨38878857798515486867352707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25919238532343657911568471 38878857798515486867352707)
      ·
        refine ⟨58318286697773230301029061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38878857798515486867352707 58318286697773230301029061)
        ·
          refine ⟨10934678755832480681442949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58318286697773230301029061 10934678755832480681442949)
          ·
            refine ⟨2050252266718590127770553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10934678755832480681442949 2050252266718590127770553)
            ·
              refine ⟨1537689200038942595827915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2050252266718590127770553 1537689200038942595827915)
              ·
                refine ⟨2306533800058413893741873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537689200038942595827915 2306533800058413893741873)
                ·
                  refine ⟨1729900350043810420306405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306533800058413893741873 1729900350043810420306405)
                  ·
                    refine ⟨324356315633214453807451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1729900350043810420306405 324356315633214453807451)
                    ·
                      rfl

theorem cell23_1895045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 2, 4].length) (baseStart_1895045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895045 prefixEnd_1895045 := by exact prefixLift 1895045
  have htrace : WordTrace (prefixWord ++ tailWord_1895045) baseStart_1895045 baseEnd_1895045 := by
    simpa [prefixWord, tailWord_1895045, baseEnd_1895045] using wordTrace_append hprefix tailTrace_1895045
  have hstable : (prefixWord ++ tailWord_1895045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895045).length < 2 ^ (prefixWord ++ tailWord_1895045).sum := by decide
  have hdescent : baseEnd_1895045 < baseStart_1895045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895051 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 3]
def baseStart_1895051 : Nat := 118140960795 + 1895051 * 2 ^ 59
def prefixEnd_1895051 : Nat := 4983230072969 + 3 ^ 40 * 1895051 * 2
def baseEnd_1895051 : Nat := 973072027783570337947325

theorem tailTrace_1895051 : CollatzResearch.WordTrace tailWord_1895051 prefixEnd_1895051 973072027783570337947325 := by
  unfold tailWord_1895051
  simp only [CollatzResearch.WordTrace]
  refine ⟨69118188257561350788901007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46078792171707567192600671 69118188257561350788901007)
  ·
    refine ⟨103677282386342026183351511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69118188257561350788901007 103677282386342026183351511)
    ·
      refine ⟨155515923579513039275027267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103677282386342026183351511 155515923579513039275027267)
      ·
        refine ⟨233273885369269558912540901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155515923579513039275027267 233273885369269558912540901)
        ·
          refine ⟨43738853506738042296101419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 233273885369269558912540901 43738853506738042296101419)
          ·
            refine ⟨65608280260107063444152129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43738853506738042296101419 65608280260107063444152129)
            ·
              refine ⟨49206210195080297583114097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65608280260107063444152129 49206210195080297583114097)
              ·
                refine ⟨36904657646310223187335573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49206210195080297583114097 36904657646310223187335573)
                ·
                  refine ⟨1729905827170791711906355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36904657646310223187335573 1729905827170791711906355)
                  ·
                    refine ⟨2594858740756187567859533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1729905827170791711906355 2594858740756187567859533)
                    ·
                      refine ⟨973072027783570337947325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594858740756187567859533 973072027783570337947325)
                      ·
                        rfl

theorem cell23_1895051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 6, 1, 3].length) (baseStart_1895051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895051 prefixEnd_1895051 := by exact prefixLift 1895051
  have htrace : WordTrace (prefixWord ++ tailWord_1895051) baseStart_1895051 baseEnd_1895051 := by
    simpa [prefixWord, tailWord_1895051, baseEnd_1895051] using wordTrace_append hprefix tailTrace_1895051
  have hstable : (prefixWord ++ tailWord_1895051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895051).length < 2 ^ (prefixWord ++ tailWord_1895051).sum := by decide
  have hdescent : baseEnd_1895051 < baseStart_1895051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895068 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 1, 3, 3]
def baseStart_1895068 : Nat := 118140960795 + 1895068 * 2 ^ 59
def prefixEnd_1895068 : Nat := 4983230072969 + 3 ^ 40 * 1895068 * 2
def baseEnd_1895068 : Nat := 973080756954696771434747

theorem tailTrace_1895068 : CollatzResearch.WordTrace tailWord_1895068 prefixEnd_1895068 973080756954696771434747 := by
  unfold tailWord_1895068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34559404149249881346134929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46079205532333175128179905 34559404149249881346134929)
  ·
    refine ⟨25919553111937411009601197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34559404149249881346134929 25919553111937411009601197)
    ·
      refine ⟨9719832416976529128600449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25919553111937411009601197 9719832416976529128600449)
      ·
        refine ⟨7289874312732396846450337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9719832416976529128600449 7289874312732396846450337)
        ·
          refine ⟨5467405734549297634837753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7289874312732396846450337 5467405734549297634837753)
          ·
            refine ⟨4100554300911973226128315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5467405734549297634837753 4100554300911973226128315)
            ·
              refine ⟨6150831451367959839192473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100554300911973226128315 6150831451367959839192473)
              ·
                refine ⟨4613123588525969879394355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6150831451367959839192473 4613123588525969879394355)
                ·
                  refine ⟨6919685382788954819091533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4613123588525969879394355 6919685382788954819091533)
                  ·
                    refine ⟨2594882018545858057159325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6919685382788954819091533 2594882018545858057159325)
                    ·
                      refine ⟨973080756954696771434747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594882018545858057159325 973080756954696771434747)
                      ·
                        rfl

theorem cell23_1895068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_1895068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895068 prefixEnd_1895068 := by exact prefixLift 1895068
  have htrace : WordTrace (prefixWord ++ tailWord_1895068) baseStart_1895068 baseEnd_1895068 := by
    simpa [prefixWord, tailWord_1895068, baseEnd_1895068] using wordTrace_append hprefix tailTrace_1895068
  have hstable : (prefixWord ++ tailWord_1895068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895068).length < 2 ^ (prefixWord ++ tailWord_1895068).sum := by decide
  have hdescent : baseEnd_1895068 < baseStart_1895068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895085 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1895085 : Nat := 118140960795 + 1895085 * 2 ^ 59
def prefixEnd_1895085 : Nat := 4983230072969 + 3 ^ 40 * 1895085 * 2
def baseEnd_1895085 : Nat := 973089486125823204922169

theorem tailTrace_1895085 : CollatzResearch.WordTrace tailWord_1895085 prefixEnd_1895085 973089486125823204922169 := by
  unfold tailWord_1895085
  simp only [CollatzResearch.WordTrace]
  refine ⟨69119428339438174595638709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46079618892958783063759139 69119428339438174595638709)
  ·
    refine ⟨6479946406822328868341129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69119428339438174595638709 6479946406822328868341129)
    ·
      refine ⟨4859959805116746651255847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6479946406822328868341129 4859959805116746651255847)
      ·
        refine ⟨7289939707675119976883771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4859959805116746651255847 7289939707675119976883771)
        ·
          refine ⟨10934909561512679965325657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7289939707675119976883771 10934909561512679965325657)
          ·
            refine ⟨8201182171134509973994243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10934909561512679965325657 8201182171134509973994243)
            ·
              refine ⟨12301773256701764960991365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201182171134509973994243 12301773256701764960991365)
              ·
                refine ⟨2306582485631580930185881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12301773256701764960991365 2306582485631580930185881)
                ·
                  refine ⟨1729936864223685697639411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306582485631580930185881 1729936864223685697639411)
                  ·
                    refine ⟨2594905296335528546459117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1729936864223685697639411 2594905296335528546459117)
                    ·
                      refine ⟨973089486125823204922169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2594905296335528546459117 973089486125823204922169)
                      ·
                        rfl

theorem cell23_1895085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1895085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895085 prefixEnd_1895085 := by exact prefixLift 1895085
  have htrace : WordTrace (prefixWord ++ tailWord_1895085) baseStart_1895085 baseEnd_1895085 := by
    simpa [prefixWord, tailWord_1895085, baseEnd_1895085] using wordTrace_append hprefix tailTrace_1895085
  have hstable : (prefixWord ++ tailWord_1895085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895085).length < 2 ^ (prefixWord ++ tailWord_1895085).sum := by decide
  have hdescent : baseEnd_1895085 < baseStart_1895085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895086 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_1895086 : Nat := 118140960795 + 1895086 * 2 ^ 59
def prefixEnd_1895086 : Nat := 4983230072969 + 3 ^ 40 * 1895086 * 2
def baseEnd_1895086 : Nat := 973089999606477701009665

theorem tailTrace_1895086 : CollatzResearch.WordTrace tailWord_1895086 prefixEnd_1895086 973089999606477701009665 := by
  unfold tailWord_1895086
  simp only [CollatzResearch.WordTrace]
  refine ⟨8639933101554318970803139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46079643208289701177616741 8639933101554318970803139)
  ·
    refine ⟨12959899652331478456204709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8639933101554318970803139 12959899652331478456204709)
    ·
      refine ⟨2429981184812152210538383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12959899652331478456204709 2429981184812152210538383)
      ·
        refine ⟨3644971777218228315807575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2429981184812152210538383 3644971777218228315807575)
        ·
          refine ⟨5467457665827342473711363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3644971777218228315807575 5467457665827342473711363)
          ·
            refine ⟨8201186498741013710567045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467457665827342473711363 8201186498741013710567045)
            ·
              refine ⟨1537722468513940070731321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8201186498741013710567045 1537722468513940070731321)
              ·
                refine ⟨1153291851385455053048491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1537722468513940070731321 1153291851385455053048491)
                ·
                  refine ⟨1729937777078182579572737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153291851385455053048491 1729937777078182579572737)
                  ·
                    refine ⟨1297453332808636934679553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1729937777078182579572737 1297453332808636934679553)
                    ·
                      refine ⟨973089999606477701009665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297453332808636934679553 973089999606477701009665)
                      ·
                        rfl

theorem cell23_1895086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_1895086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895086 prefixEnd_1895086 := by exact prefixLift 1895086
  have htrace : WordTrace (prefixWord ++ tailWord_1895086) baseStart_1895086 baseEnd_1895086 := by
    simpa [prefixWord, tailWord_1895086, baseEnd_1895086] using wordTrace_append hprefix tailTrace_1895086
  have hstable : (prefixWord ++ tailWord_1895086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895086).length < 2 ^ (prefixWord ++ tailWord_1895086).sum := by decide
  have hdescent : baseEnd_1895086 < baseStart_1895086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895101 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1895101 : Nat := 118140960795 + 1895101 * 2 ^ 59
def prefixEnd_1895101 : Nat := 4983230072969 + 3 ^ 40 * 1895101 * 2
def baseEnd_1895101 : Nat := 324365900605431714107365

theorem tailTrace_1895101 : CollatzResearch.WordTrace tailWord_1895101 prefixEnd_1895101 324365900605431714107365 := by
  unfold tailWord_1895101
  simp only [CollatzResearch.WordTrace]
  refine ⟨69120011907380209328221157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46080007938253472885480771 69120011907380209328221157)
  ·
    refine ⟨12960002232633789249041467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69120011907380209328221157 12960002232633789249041467)
    ·
      refine ⟨19440003348950683873562201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12960002232633789249041467 19440003348950683873562201)
      ·
        refine ⟨14580002511713012905171651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19440003348950683873562201 14580002511713012905171651)
        ·
          refine ⟨21870003767569519357757477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580002511713012905171651 21870003767569519357757477)
          ·
            refine ⟨4100625706419284879579527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21870003767569519357757477 4100625706419284879579527)
            ·
              refine ⟨6150938559628927319369291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4100625706419284879579527 6150938559628927319369291)
              ·
                refine ⟨9226407839443390979053937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6150938559628927319369291 9226407839443390979053937)
                ·
                  refine ⟨6919805879582543234290453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9226407839443390979053937 6919805879582543234290453)
                  ·
                    refine ⟨324365900605431714107365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6919805879582543234290453 324365900605431714107365)
                    ·
                      rfl

theorem cell23_1895101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1895101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895101 prefixEnd_1895101 := by exact prefixLift 1895101
  have htrace : WordTrace (prefixWord ++ tailWord_1895101) baseStart_1895101 baseEnd_1895101 := by
    simpa [prefixWord, tailWord_1895101, baseEnd_1895101] using wordTrace_append hprefix tailTrace_1895101
  have hstable : (prefixWord ++ tailWord_1895101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895101).length < 2 ^ (prefixWord ++ tailWord_1895101).sum := by decide
  have hdescent : baseEnd_1895101 < baseStart_1895101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895158 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1895158 : Nat := 118140960795 + 1895158 * 2 ^ 59
def prefixEnd_1895158 : Nat := 4983230072969 + 3 ^ 40 * 1895158 * 2
def baseEnd_1895158 : Nat := 973126970213601419309333

theorem tailTrace_1895158 : CollatzResearch.WordTrace tailWord_1895158 prefixEnd_1895158 973126970213601419309333 := by
  unfold tailWord_1895158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4320130679260856753940383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46081393912115805375364085 4320130679260856753940383)
  ·
    refine ⟨6480196018891285130910575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4320130679260856753940383 6480196018891285130910575)
    ·
      refine ⟨9720294028336927696365863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6480196018891285130910575 9720294028336927696365863)
      ·
        refine ⟨14580441042505391544548795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9720294028336927696365863 14580441042505391544548795)
        ·
          refine ⟨21870661563758087316823193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14580441042505391544548795 21870661563758087316823193)
          ·
            refine ⟨16402996172818565487617395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21870661563758087316823193 16402996172818565487617395)
            ·
              refine ⟨24604494259227848231426093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16402996172818565487617395 24604494259227848231426093)
              ·
                refine ⟨9226685347210443086784785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24604494259227848231426093 9226685347210443086784785)
                ·
                  refine ⟨6920014010407832315088589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9226685347210443086784785 6920014010407832315088589)
                  ·
                    refine ⟨2595005253902937118158221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6920014010407832315088589 2595005253902937118158221)
                    ·
                      refine ⟨973126970213601419309333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595005253902937118158221 973126970213601419309333)
                      ·
                        rfl

theorem cell23_1895158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1895158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895158 prefixEnd_1895158 := by exact prefixLift 1895158
  have htrace : WordTrace (prefixWord ++ tailWord_1895158) baseStart_1895158 baseEnd_1895158 := by
    simpa [prefixWord, tailWord_1895158, baseEnd_1895158] using wordTrace_append hprefix tailTrace_1895158
  have hstable : (prefixWord ++ tailWord_1895158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895158).length < 2 ^ (prefixWord ++ tailWord_1895158).sum := by decide
  have hdescent : baseEnd_1895158 < baseStart_1895158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895218 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1895218 : Nat := 118140960795 + 1895218 * 2 ^ 59
def prefixEnd_1895218 : Nat := 4983230072969 + 3 ^ 40 * 1895218 * 2
def baseEnd_1895218 : Nat := 973157779052871184559057

theorem tailTrace_1895218 : CollatzResearch.WordTrace tailWord_1895218 prefixEnd_1895218 973157779052871184559057 := by
  unfold tailWord_1895218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17281069811989084577557577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46082852831970892206820205 17281069811989084577557577)
  ·
    refine ⟨12960802358991813433168183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17281069811989084577557577 12960802358991813433168183)
    ·
      refine ⟨19441203538487720149752275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12960802358991813433168183 19441203538487720149752275)
      ·
        refine ⟨29161805307731580224628413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19441203538487720149752275 29161805307731580224628413)
        ·
          refine ⟨10935676990399342584235655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29161805307731580224628413 10935676990399342584235655)
          ·
            refine ⟨16403515485599013876353483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10935676990399342584235655 16403515485599013876353483)
            ·
              refine ⟨24605273228398520814530225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16403515485599013876353483 24605273228398520814530225)
              ·
                refine ⟨18453954921298890610897669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24605273228398520814530225 18453954921298890610897669)
                ·
                  refine ⟨3460116547743541989543313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18453954921298890610897669 3460116547743541989543313)
                  ·
                    refine ⟨2595087410807656492157485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3460116547743541989543313 2595087410807656492157485)
                    ·
                      refine ⟨973157779052871184559057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595087410807656492157485 973157779052871184559057)
                      ·
                        rfl

theorem cell23_1895218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1895218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895218 prefixEnd_1895218 := by exact prefixLift 1895218
  have htrace : WordTrace (prefixWord ++ tailWord_1895218) baseStart_1895218 baseEnd_1895218 := by
    simpa [prefixWord, tailWord_1895218, baseEnd_1895218] using wordTrace_append hprefix tailTrace_1895218
  have hstable : (prefixWord ++ tailWord_1895218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895218).length < 2 ^ (prefixWord ++ tailWord_1895218).sum := by decide
  have hdescent : baseEnd_1895218 < baseStart_1895218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895268 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1895268 : Nat := 118140960795 + 1895268 * 2 ^ 59
def prefixEnd_1895268 : Nat := 4983230072969 + 3 ^ 40 * 1895268 * 2
def baseEnd_1895268 : Nat := 324394484361865329644609

theorem tailTrace_1895268 : CollatzResearch.WordTrace tailWord_1895268 prefixEnd_1895268 324394484361865329644609 := by
  unfold tailWord_1895268
  simp only [CollatzResearch.WordTrace]
  refine ⟨34563051448887598424775229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46084068598516797899700305 34563051448887598424775229)
  ·
    refine ⟨12961144293332849409290711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34563051448887598424775229 12961144293332849409290711)
    ·
      refine ⟨19441716439999274113936067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12961144293332849409290711 19441716439999274113936067)
      ·
        refine ⟨29162574659998911170904101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19441716439999274113936067 29162574659998911170904101)
        ·
          refine ⟨5467982748749795844544519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29162574659998911170904101 5467982748749795844544519)
          ·
            refine ⟨8201974123124693766816779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5467982748749795844544519 8201974123124693766816779)
            ·
              refine ⟨12302961184687040650225169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8201974123124693766816779 12302961184687040650225169)
              ·
                refine ⟨9227220888515280487668877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12302961184687040650225169 9227220888515280487668877)
                ·
                  refine ⟨3460207833193230182875829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9227220888515280487668877 3460207833193230182875829)
                  ·
                    refine ⟨324394484361865329644609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3460207833193230182875829 324394484361865329644609)
                    ·
                      rfl

theorem cell23_1895268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1895268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895268 prefixEnd_1895268 := by exact prefixLift 1895268
  have htrace : WordTrace (prefixWord ++ tailWord_1895268) baseStart_1895268 baseEnd_1895268 := by
    simpa [prefixWord, tailWord_1895268, baseEnd_1895268] using wordTrace_append hprefix tailTrace_1895268
  have hstable : (prefixWord ++ tailWord_1895268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895268).length < 2 ^ (prefixWord ++ tailWord_1895268).sum := by decide
  have hdescent : baseEnd_1895268 < baseStart_1895268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895288 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 8, 2]
def baseStart_1895288 : Nat := 118140960795 + 1895288 * 2 ^ 59
def prefixEnd_1895288 : Nat := 4983230072969 + 3 ^ 40 * 1895288 * 2
def baseEnd_1895288 : Nat := 973193722698685910683735

theorem tailTrace_1895288 : CollatzResearch.WordTrace tailWord_1895288 prefixEnd_1895288 973193722698685910683735 := by
  unfold tailWord_1895288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34563416178851370132639259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46084554905135160176852345 34563416178851370132639259)
  ·
    refine ⟨51845124268277055198958889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34563416178851370132639259 51845124268277055198958889)
    ·
      refine ⟨38883843201207791399219167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51845124268277055198958889 38883843201207791399219167)
      ·
        refine ⟨58325764801811687098828751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38883843201207791399219167 58325764801811687098828751)
        ·
          refine ⟨87488647202717530648243127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58325764801811687098828751 87488647202717530648243127)
          ·
            refine ⟨131232970804076295972364691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87488647202717530648243127 131232970804076295972364691)
            ·
              refine ⟨196849456206114443958547037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131232970804076295972364691 196849456206114443958547037)
              ·
                refine ⟨73818546077292916484455139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196849456206114443958547037 73818546077292916484455139)
                ·
                  refine ⟨110727819115939374726682709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73818546077292916484455139 110727819115939374726682709)
                  ·
                    refine ⟨1297591630264914547578313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110727819115939374726682709 1297591630264914547578313)
                    ·
                      refine ⟨973193722698685910683735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297591630264914547578313 973193722698685910683735)
                      ·
                        rfl

theorem cell23_1895288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 8, 2].length) (baseStart_1895288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895288 prefixEnd_1895288 := by exact prefixLift 1895288
  have htrace : WordTrace (prefixWord ++ tailWord_1895288) baseStart_1895288 baseEnd_1895288 := by
    simpa [prefixWord, tailWord_1895288, baseEnd_1895288] using wordTrace_append hprefix tailTrace_1895288
  have hstable : (prefixWord ++ tailWord_1895288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895288).length < 2 ^ (prefixWord ++ tailWord_1895288).sum := by decide
  have hdescent : baseEnd_1895288 < baseStart_1895288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895305 : List Nat := [1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 4]
def baseStart_1895305 : Nat := 118140960795 + 1895305 * 2 ^ 59
def prefixEnd_1895305 : Nat := 4983230072969 + 3 ^ 40 * 1895305 * 2
def baseEnd_1895305 : Nat := 973202451869812344171157

theorem tailTrace_1895305 : CollatzResearch.WordTrace tailWord_1895305 prefixEnd_1895305 973202451869812344171157 := by
  unfold tailWord_1895305
  simp only [CollatzResearch.WordTrace]
  refine ⟨69127452398641152168647369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46084968265760768112431579 69127452398641152168647369)
  ·
    refine ⟨51845589298980864126485527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69127452398641152168647369 51845589298980864126485527)
    ·
      refine ⟨77768383948471296189728291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51845589298980864126485527 77768383948471296189728291)
      ·
        refine ⟨116652575922706944284592437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77768383948471296189728291 116652575922706944284592437)
        ·
          refine ⟨10936178992753776026680541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 116652575922706944284592437 10936178992753776026680541)
          ·
            refine ⟨4101067122282666010005203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10936178992753776026680541 4101067122282666010005203)
            ·
              refine ⟨6151600683423999015007805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101067122282666010005203 6151600683423999015007805)
              ·
                refine ⟨2306850256283999630627927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6151600683423999015007805 2306850256283999630627927)
                ·
                  refine ⟨3460275384425999445941891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306850256283999630627927 3460275384425999445941891)
                  ·
                    refine ⟨5190413076638999168912837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3460275384425999445941891 5190413076638999168912837)
                    ·
                      refine ⟨973202451869812344171157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5190413076638999168912837 973202451869812344171157)
                      ·
                        rfl

theorem cell23_1895305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_1895305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895305 prefixEnd_1895305 := by exact prefixLift 1895305
  have htrace : WordTrace (prefixWord ++ tailWord_1895305) baseStart_1895305 baseEnd_1895305 := by
    simpa [prefixWord, tailWord_1895305, baseEnd_1895305] using wordTrace_append hprefix tailTrace_1895305
  have hstable : (prefixWord ++ tailWord_1895305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895305).length < 2 ^ (prefixWord ++ tailWord_1895305).sum := by decide
  have hdescent : baseEnd_1895305 < baseStart_1895305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895321 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1895321 : Nat := 118140960795 + 1895321 * 2 ^ 59
def prefixEnd_1895321 : Nat := 4983230072969 + 3 ^ 40 * 1895321 * 2
def baseEnd_1895321 : Nat := 973210667560284281571083

theorem tailTrace_1895321 : CollatzResearch.WordTrace tailWord_1895321 prefixEnd_1895321 973210667560284281571083 := by
  unfold tailWord_1895321
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128035966583186901229817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46085357311055457934153211 69128035966583186901229817)
  ·
    refine ⟨51846026974937390175922363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69128035966583186901229817 51846026974937390175922363)
    ·
      refine ⟨77769040462406085263883545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51846026974937390175922363 77769040462406085263883545)
      ·
        refine ⟨58326780346804563947912659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77769040462406085263883545 58326780346804563947912659)
        ·
          refine ⟨87490170520206845921868989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58326780346804563947912659 87490170520206845921868989)
          ·
            refine ⟨32808813945077567220700871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87490170520206845921868989 32808813945077567220700871)
            ·
              refine ⟨49213220917616350831051307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32808813945077567220700871 49213220917616350831051307)
              ·
                refine ⟨73819831376424526246576961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49213220917616350831051307 73819831376424526246576961)
                ·
                  refine ⟨55364873532318394684932721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73819831376424526246576961 55364873532318394684932721)
                  ·
                    refine ⟨41523655149238796013699541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 55364873532318394684932721 41523655149238796013699541)
                    ·
                      refine ⟨973210667560284281571083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41523655149238796013699541 973210667560284281571083)
                      ·
                        rfl

theorem cell23_1895321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1895321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895321 prefixEnd_1895321 := by exact prefixLift 1895321
  have htrace : WordTrace (prefixWord ++ tailWord_1895321) baseStart_1895321 baseEnd_1895321 := by
    simpa [prefixWord, tailWord_1895321, baseEnd_1895321] using wordTrace_append hprefix tailTrace_1895321
  have hstable : (prefixWord ++ tailWord_1895321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895321).length < 2 ^ (prefixWord ++ tailWord_1895321).sum := by decide
  have hdescent : baseEnd_1895321 < baseStart_1895321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895332 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1895332 : Nat := 118140960795 + 1895332 * 2 ^ 59
def prefixEnd_1895332 : Nat := 4983230072969 + 3 ^ 40 * 1895332 * 2
def baseEnd_1895332 : Nat := 324405438615827912844511

theorem tailTrace_1895332 : CollatzResearch.WordTrace tailWord_1895332 prefixEnd_1895332 324405438615827912844511 := by
  unfold tailWord_1895332
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564218584771667889940125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46085624779695557186586833 34564218584771667889940125)
  ·
    refine ⟨12961581969289375458727547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34564218584771667889940125 12961581969289375458727547)
    ·
      refine ⟨19442372953934063188091321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12961581969289375458727547 19442372953934063188091321)
      ·
        refine ⟨14581779715450547391068491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19442372953934063188091321 14581779715450547391068491)
        ·
          refine ⟨21872669573175821086602737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14581779715450547391068491 21872669573175821086602737)
          ·
            refine ⟨16404502179881865814952053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21872669573175821086602737 16404502179881865814952053)
            ·
              refine ⟨1537922079363924920151755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16404502179881865814952053 1537922079363924920151755)
              ·
                refine ⟨2306883119045887380227633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1537922079363924920151755 2306883119045887380227633)
                ·
                  refine ⟨1730162339284415535170725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306883119045887380227633 1730162339284415535170725)
                  ·
                    refine ⟨324405438615827912844511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730162339284415535170725 324405438615827912844511)
                    ·
                      rfl

theorem cell23_1895332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1895332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895332 prefixEnd_1895332 := by exact prefixLift 1895332
  have htrace : WordTrace (prefixWord ++ tailWord_1895332) baseStart_1895332 baseEnd_1895332 := by
    simpa [prefixWord, tailWord_1895332, baseEnd_1895332] using wordTrace_append hprefix tailTrace_1895332
  have hstable : (prefixWord ++ tailWord_1895332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895332).length < 2 ^ (prefixWord ++ tailWord_1895332).sum := by decide
  have hdescent : baseEnd_1895332 < baseStart_1895332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895335 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1895335 : Nat := 118140960795 + 1895335 * 2 ^ 59
def prefixEnd_1895335 : Nat := 4983230072969 + 3 ^ 40 * 1895335 * 2
def baseEnd_1895335 : Nat := 973217856289447226796019

theorem tailTrace_1895335 : CollatzResearch.WordTrace tailWord_1895335 prefixEnd_1895335 973217856289447226796019 := by
  unfold tailWord_1895335
  simp only [CollatzResearch.WordTrace]
  refine ⟨69128546588532467292239459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46085697725688311528159639 69128546588532467292239459)
  ·
    refine ⟨103692819882798700938359189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69128546588532467292239459 103692819882798700938359189)
    ·
      refine ⟨4860600932006189106485587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103692819882798700938359189 4860600932006189106485587)
      ·
        refine ⟨7290901398009283659728381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4860600932006189106485587 7290901398009283659728381)
        ·
          refine ⟨2734088024253481372398143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7290901398009283659728381 2734088024253481372398143)
          ·
            refine ⟨4101132036380222058597215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734088024253481372398143 4101132036380222058597215)
            ·
              refine ⟨6151698054570333087895823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101132036380222058597215 6151698054570333087895823)
              ·
                refine ⟨9227547081855499631843735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6151698054570333087895823 9227547081855499631843735)
                ·
                  refine ⟨13841320622783249447765603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9227547081855499631843735 13841320622783249447765603)
                  ·
                    refine ⟨20761980934174874171648405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13841320622783249447765603 20761980934174874171648405)
                    ·
                      refine ⟨973217856289447226796019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20761980934174874171648405 973217856289447226796019)
                      ·
                        rfl

theorem cell23_1895335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1895335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895335 prefixEnd_1895335 := by exact prefixLift 1895335
  have htrace : WordTrace (prefixWord ++ tailWord_1895335) baseStart_1895335 baseEnd_1895335 := by
    simpa [prefixWord, tailWord_1895335, baseEnd_1895335] using wordTrace_append hprefix tailTrace_1895335
  have hstable : (prefixWord ++ tailWord_1895335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895335).length < 2 ^ (prefixWord ++ tailWord_1895335).sum := by decide
  have hdescent : baseEnd_1895335 < baseStart_1895335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895372 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1895372 : Nat := 118140960795 + 1895372 * 2 ^ 59
def prefixEnd_1895372 : Nat := 4983230072969 + 3 ^ 40 * 1895372 * 2
def baseEnd_1895372 : Nat := 973236855073663582033349

theorem tailTrace_1895372 : CollatzResearch.WordTrace tailWord_1895372 prefixEnd_1895372 973236855073663582033349 := by
  unfold tailWord_1895372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34564948044699211305668185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46086597392932281740890913 34564948044699211305668185)
  ·
    refine ⟨25923711033524408479251139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34564948044699211305668185 25923711033524408479251139)
    ·
      refine ⟨38885566550286612718876709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25923711033524408479251139 38885566550286612718876709)
      ·
        refine ⟨7291043728178739884789383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38885566550286612718876709 7291043728178739884789383)
        ·
          refine ⟨10936565592268109827184075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291043728178739884789383 10936565592268109827184075)
          ·
            refine ⟨16404848388402164740776113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10936565592268109827184075 16404848388402164740776113)
            ·
              refine ⟨12303636291301623555582085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16404848388402164740776113 12303636291301623555582085)
              ·
                refine ⟨2306931804619054416671641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12303636291301623555582085 2306931804619054416671641)
                ·
                  refine ⟨1730198853464290812503731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306931804619054416671641 1730198853464290812503731)
                  ·
                    refine ⟨2595298280196436218755597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730198853464290812503731 2595298280196436218755597)
                    ·
                      refine ⟨973236855073663582033349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595298280196436218755597 973236855073663582033349)
                      ·
                        rfl

theorem cell23_1895372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1895372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895372 prefixEnd_1895372 := by exact prefixLift 1895372
  have htrace : WordTrace (prefixWord ++ tailWord_1895372) baseStart_1895372 baseEnd_1895372 := by
    simpa [prefixWord, tailWord_1895372, baseEnd_1895372] using wordTrace_append hprefix tailTrace_1895372
  have hstable : (prefixWord ++ tailWord_1895372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895372).length < 2 ^ (prefixWord ++ tailWord_1895372).sum := by decide
  have hdescent : baseEnd_1895372 < baseStart_1895372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895389 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1895389 : Nat := 118140960795 + 1895389 * 2 ^ 59
def prefixEnd_1895389 : Nat := 4983230072969 + 3 ^ 40 * 1895389 * 2
def baseEnd_1895389 : Nat := 973245584244790015520771

theorem tailTrace_1895389 : CollatzResearch.WordTrace tailWord_1895389 prefixEnd_1895389 973245584244790015520771 := by
  unfold tailWord_1895389
  simp only [CollatzResearch.WordTrace]
  refine ⟨69130516130336834514705221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46087010753557889676470147 69130516130336834514705221)
  ·
    refine ⟨12961971774438156471507229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69130516130336834514705221 12961971774438156471507229)
    ·
      refine ⟨4860739415414308676815211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12961971774438156471507229 4860739415414308676815211)
      ·
        refine ⟨7291109123121463015222817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4860739415414308676815211 7291109123121463015222817)
        ·
          refine ⟨5468331842341097261417113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7291109123121463015222817 5468331842341097261417113)
          ·
            refine ⟨4101248881755822946062835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5468331842341097261417113 4101248881755822946062835)
            ·
              refine ⟨6151873322633734419094253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101248881755822946062835 6151873322633734419094253)
              ·
                refine ⟨2306952495987650407160345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6151873322633734419094253 2306952495987650407160345)
                ·
                  refine ⟨1730214371990737805370259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2306952495987650407160345 1730214371990737805370259)
                  ·
                    refine ⟨2595321557986106708055389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730214371990737805370259 2595321557986106708055389)
                    ·
                      refine ⟨973245584244790015520771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595321557986106708055389 973245584244790015520771)
                      ·
                        rfl

theorem cell23_1895389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1895389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895389 prefixEnd_1895389 := by exact prefixLift 1895389
  have htrace : WordTrace (prefixWord ++ tailWord_1895389) baseStart_1895389 baseEnd_1895389 := by
    simpa [prefixWord, tailWord_1895389, baseEnd_1895389] using wordTrace_append hprefix tailTrace_1895389
  have hstable : (prefixWord ++ tailWord_1895389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895389).length < 2 ^ (prefixWord ++ tailWord_1895389).sum := by decide
  have hdescent : baseEnd_1895389 < baseStart_1895389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895399 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 1, 3, 2]
def baseStart_1895399 : Nat := 118140960795 + 1895399 * 2 ^ 59
def prefixEnd_1895399 : Nat := 4983230072969 + 3 ^ 40 * 1895399 * 2
def baseEnd_1895399 : Nat := 973250719051334976395725

theorem tailTrace_1895399 : CollatzResearch.WordTrace tailWord_1895399 prefixEnd_1895399 973250719051334976395725 := by
  unfold tailWord_1895399
  simp only [CollatzResearch.WordTrace]
  refine ⟨69130880860300606222569251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46087253906867070815046167 69130880860300606222569251)
  ·
    refine ⟨103696321290450909333853877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69130880860300606222569251 103696321290450909333853877)
    ·
      refine ⟨9721530120979772750048801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103696321290450909333853877 9721530120979772750048801)
      ·
        refine ⟨7291147590734829562536601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9721530120979772750048801 7291147590734829562536601)
        ·
          refine ⟨5468360693051122171902451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7291147590734829562536601 5468360693051122171902451)
          ·
            refine ⟨8202541039576683257853677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468360693051122171902451 8202541039576683257853677)
            ·
              refine ⟨3075952889841256221695129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8202541039576683257853677 3075952889841256221695129)
              ·
                refine ⟨2306964667380942166271347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3075952889841256221695129 2306964667380942166271347)
                ·
                  refine ⟨3460447001071413249407021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2306964667380942166271347 3460447001071413249407021)
                  ·
                    refine ⟨1297667625401779968527633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3460447001071413249407021 1297667625401779968527633)
                    ·
                      refine ⟨973250719051334976395725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297667625401779968527633 973250719051334976395725)
                      ·
                        rfl

theorem cell23_1895399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_1895399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895399 prefixEnd_1895399 := by exact prefixLift 1895399
  have htrace : WordTrace (prefixWord ++ tailWord_1895399) baseStart_1895399 baseEnd_1895399 := by
    simpa [prefixWord, tailWord_1895399, baseEnd_1895399] using wordTrace_append hprefix tailTrace_1895399
  have hstable : (prefixWord ++ tailWord_1895399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895399).length < 2 ^ (prefixWord ++ tailWord_1895399).sum := by decide
  have hdescent : baseEnd_1895399 < baseStart_1895399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895408 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4]
def baseStart_1895408 : Nat := 118140960795 + 1895408 * 2 ^ 59
def prefixEnd_1895408 : Nat := 4983230072969 + 3 ^ 40 * 1895408 * 2
def baseEnd_1895408 : Nat := 973255340377225441183183

theorem tailTrace_1895408 : CollatzResearch.WordTrace tailWord_1895408 prefixEnd_1895408 973255340377225441183183 := by
  unfold tailWord_1895408
  simp only [CollatzResearch.WordTrace]
  refine ⟨34565604558634000379823439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46087472744845333839764585 34565604558634000379823439)
  ·
    refine ⟨51848406837951000569735159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34565604558634000379823439 51848406837951000569735159)
    ·
      refine ⟨77772610256926500854602739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51848406837951000569735159 77772610256926500854602739)
      ·
        refine ⟨116658915385389751281904109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77772610256926500854602739 116658915385389751281904109)
        ·
          refine ⟨43747093269521156730714041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116658915385389751281904109 43747093269521156730714041)
          ·
            refine ⟨32810319952140867548035531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43747093269521156730714041 32810319952140867548035531)
            ·
              refine ⟨49215479928211301322053297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32810319952140867548035531 49215479928211301322053297)
              ·
                refine ⟨36911609946158475991539973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49215479928211301322053297 36911609946158475991539973)
                ·
                  refine ⟨6920926864904714248413745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36911609946158475991539973 6920926864904714248413745)
                  ·
                    refine ⟨5190695148678535686310309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6920926864904714248413745 5190695148678535686310309)
                    ·
                      refine ⟨973255340377225441183183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5190695148678535686310309 973255340377225441183183)
                      ·
                        rfl

theorem cell23_1895408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_1895408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895408 prefixEnd_1895408 := by exact prefixLift 1895408
  have htrace : WordTrace (prefixWord ++ tailWord_1895408) baseStart_1895408 baseEnd_1895408 := by
    simpa [prefixWord, tailWord_1895408, baseEnd_1895408] using wordTrace_append hprefix tailTrace_1895408
  have hstable : (prefixWord ++ tailWord_1895408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895408).length < 2 ^ (prefixWord ++ tailWord_1895408).sum := by decide
  have hdescent : baseEnd_1895408 < baseStart_1895408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895429 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 2, 2, 2]
def baseStart_1895429 : Nat := 118140960795 + 1895429 * 2 ^ 59
def prefixEnd_1895429 : Nat := 4983230072969 + 3 ^ 40 * 1895429 * 2
def baseEnd_1895429 : Nat := 973266123470969859020587

theorem tailTrace_1895429 : CollatzResearch.WordTrace tailWord_1895429 prefixEnd_1895429 973266123470969859020587 := by
  unfold tailWord_1895429
  simp only [CollatzResearch.WordTrace]
  refine ⟨69131975050191921346161341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46087983366794614230774227 69131975050191921346161341)
  ·
    refine ⟨25924490643821970504810503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69131975050191921346161341 25924490643821970504810503)
    ·
      refine ⟨38886735965732955757215755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25924490643821970504810503 38886735965732955757215755)
      ·
        refine ⟨58330103948599433635823633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38886735965732955757215755 58330103948599433635823633)
        ·
          refine ⟨43747577961449575226867725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58330103948599433635823633 43747577961449575226867725)
          ·
            refine ⟨16405341735543590710075397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43747577961449575226867725 16405341735543590710075397)
            ·
              refine ⟨3076001575414423258139137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16405341735543590710075397 3076001575414423258139137)
              ·
                refine ⟨2307001181560817443604353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076001575414423258139137 2307001181560817443604353)
                ·
                  refine ⟨1730250886170613082703265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307001181560817443604353 1730250886170613082703265)
                  ·
                    refine ⟨1297688164627959812027449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1730250886170613082703265 1297688164627959812027449)
                    ·
                      refine ⟨973266123470969859020587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297688164627959812027449 973266123470969859020587)
                      ·
                        rfl

theorem cell23_1895429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 2, 2, 2].length) (baseStart_1895429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895429 prefixEnd_1895429 := by exact prefixLift 1895429
  have htrace : WordTrace (prefixWord ++ tailWord_1895429) baseStart_1895429 baseEnd_1895429 := by
    simpa [prefixWord, tailWord_1895429, baseEnd_1895429] using wordTrace_append hprefix tailTrace_1895429
  have hstable : (prefixWord ++ tailWord_1895429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895429).length < 2 ^ (prefixWord ++ tailWord_1895429).sum := by decide
  have hdescent : baseEnd_1895429 < baseStart_1895429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895445 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 3]
def baseStart_1895445 : Nat := 118140960795 + 1895445 * 2 ^ 59
def prefixEnd_1895445 : Nat := 4983230072969 + 3 ^ 40 * 1895445 * 2
def baseEnd_1895445 : Nat := 973274339161441796420513

theorem tailTrace_1895445 : CollatzResearch.WordTrace tailWord_1895445 prefixEnd_1895445 973274339161441796420513 := by
  unfold tailWord_1895445
  simp only [CollatzResearch.WordTrace]
  refine ⟨69132558618133956078743789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46088372412089304052495859 69132558618133956078743789)
  ·
    refine ⟨25924709481800233529528921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69132558618133956078743789 25924709481800233529528921)
    ·
      refine ⟨19443532111350175147146691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25924709481800233529528921 19443532111350175147146691)
      ·
        refine ⟨29165298167025262720720037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19443532111350175147146691 29165298167025262720720037)
        ·
          refine ⟨5468493406317236760135007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29165298167025262720720037 5468493406317236760135007)
          ·
            refine ⟨8202740109475855140202511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5468493406317236760135007 8202740109475855140202511)
            ·
              refine ⟨12304110164213782710303767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8202740109475855140202511 12304110164213782710303767)
              ·
                refine ⟨18456165246320674065455651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12304110164213782710303767 18456165246320674065455651)
                ·
                  refine ⟨27684247869481011098183477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18456165246320674065455651 27684247869481011098183477)
                  ·
                    refine ⟨2595398237763844790454701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27684247869481011098183477 2595398237763844790454701)
                    ·
                      refine ⟨973274339161441796420513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595398237763844790454701 973274339161441796420513)
                      ·
                        rfl

theorem cell23_1895445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_1895445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895445 prefixEnd_1895445 := by exact prefixLift 1895445
  have htrace : WordTrace (prefixWord ++ tailWord_1895445) baseStart_1895445 baseEnd_1895445 := by
    simpa [prefixWord, tailWord_1895445, baseEnd_1895445] using wordTrace_append hprefix tailTrace_1895445
  have hstable : (prefixWord ++ tailWord_1895445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895445).length < 2 ^ (prefixWord ++ tailWord_1895445).sum := by decide
  have hdescent : baseEnd_1895445 < baseStart_1895445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895502 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_1895502 : Nat := 118140960795 + 1895502 * 2 ^ 59
def prefixEnd_1895502 : Nat := 4983230072969 + 3 ^ 40 * 1895502 * 2
def baseEnd_1895502 : Nat := 973303607558748073407751

theorem tailTrace_1895502 : CollatzResearch.WordTrace tailWord_1895502 prefixEnd_1895502 973303607558748073407751 := by
  unfold tailWord_1895502
  simp only [CollatzResearch.WordTrace]
  refine ⟨8641829697365931851696095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46089758385951636542379173 8641829697365931851696095)
  ·
    refine ⟨12962744546048897777544143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8641829697365931851696095 12962744546048897777544143)
    ·
      refine ⟨19444116819073346666316215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12962744546048897777544143 19444116819073346666316215)
      ·
        refine ⟨29166175228610019999474323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19444116819073346666316215 29166175228610019999474323)
        ·
          refine ⟨43749262842915029999211485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29166175228610019999474323 43749262842915029999211485)
          ·
            refine ⟨16405973566093136249704307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43749262842915029999211485 16405973566093136249704307)
            ·
              refine ⟨24608960349139704374556461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16405973566093136249704307 24608960349139704374556461)
              ·
                refine ⟨9228360130927389140458673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24608960349139704374556461 9228360130927389140458673)
                ·
                  refine ⟨6921270098195541855344005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9228360130927389140458673 6921270098195541855344005)
                  ·
                    refine ⟨1297738143411664097877001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6921270098195541855344005 1297738143411664097877001)
                    ·
                      refine ⟨973303607558748073407751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297738143411664097877001 973303607558748073407751)
                      ·
                        rfl

theorem cell23_1895502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_1895502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895502 prefixEnd_1895502 := by exact prefixLift 1895502
  have htrace : WordTrace (prefixWord ++ tailWord_1895502) baseStart_1895502 baseEnd_1895502 := by
    simpa [prefixWord, tailWord_1895502, baseEnd_1895502] using wordTrace_append hprefix tailTrace_1895502
  have hstable : (prefixWord ++ tailWord_1895502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895502).length < 2 ^ (prefixWord ++ tailWord_1895502).sum := by decide
  have hdescent : baseEnd_1895502 < baseStart_1895502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895505 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_1895505 : Nat := 118140960795 + 1895505 * 2 ^ 59
def prefixEnd_1895505 : Nat := 4983230072969 + 3 ^ 40 * 1895505 * 2
def baseEnd_1895505 : Nat := 973305148000711561670237

theorem tailTrace_1895505 : CollatzResearch.WordTrace tailWord_1895505 prefixEnd_1895505 973305148000711561670237 := by
  unfold tailWord_1895505
  simp only [CollatzResearch.WordTrace]
  refine ⟨69134746997916586325927969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46089831331944390883951979 69134746997916586325927969)
  ·
    refine ⟨51851060248437439744445977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69134746997916586325927969 51851060248437439744445977)
    ·
      refine ⟨38888295186328079808334483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51851060248437439744445977 38888295186328079808334483)
      ·
        refine ⟨58332442779492119712501725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38888295186328079808334483 58332442779492119712501725)
        ·
          refine ⟨21874666042309544892188147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58332442779492119712501725 21874666042309544892188147)
          ·
            refine ⟨32811999063464317338282221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21874666042309544892188147 32811999063464317338282221)
            ·
              refine ⟨12304499648799119001855833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32811999063464317338282221 12304499648799119001855833)
              ·
                refine ⟨9228374736599339251391875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12304499648799119001855833 9228374736599339251391875)
                ·
                  refine ⟨13842562104899008877087813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9228374736599339251391875 13842562104899008877087813)
                  ·
                    refine ⟨2595480394668564164453965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13842562104899008877087813 2595480394668564164453965)
                    ·
                      refine ⟨973305148000711561670237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595480394668564164453965 973305148000711561670237)
                      ·
                        rfl

theorem cell23_1895505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_1895505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895505 prefixEnd_1895505 := by exact prefixLift 1895505
  have htrace : WordTrace (prefixWord ++ tailWord_1895505) baseStart_1895505 baseEnd_1895505 := by
    simpa [prefixWord, tailWord_1895505, baseEnd_1895505] using wordTrace_append hprefix tailTrace_1895505
  have hstable : (prefixWord ++ tailWord_1895505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895505).length < 2 ^ (prefixWord ++ tailWord_1895505).sum := by decide
  have hdescent : baseEnd_1895505 < baseStart_1895505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895529 : List Nat := [1, 2, 1, 1, 1, 6, 3, 3, 1, 4]
def baseStart_1895529 : Nat := 118140960795 + 1895529 * 2 ^ 59
def prefixEnd_1895529 : Nat := 4983230072969 + 3 ^ 40 * 1895529 * 2
def baseEnd_1895529 : Nat := 324439157178806489256709

theorem tailTrace_1895529 : CollatzResearch.WordTrace tailWord_1895529 prefixEnd_1895529 324439157178806489256709 := by
  unfold tailWord_1895529
  simp only [CollatzResearch.WordTrace]
  refine ⟨69135622349829638424801641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46090414899886425616534427 69135622349829638424801641)
  ·
    refine ⟨51851716762372228818601231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69135622349829638424801641 51851716762372228818601231)
    ·
      refine ⟨77777575143558343227901847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51851716762372228818601231 77777575143558343227901847)
      ·
        refine ⟨116666362715337514841852771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77777575143558343227901847 116666362715337514841852771)
        ·
          refine ⟨174999544073006272262779157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116666362715337514841852771 174999544073006272262779157)
          ·
            refine ⟨8203103628422169012317773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 174999544073006272262779157 8203103628422169012317773)
            ·
              refine ⟨3076163860658313379619165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8203103628422169012317773 3076163860658313379619165)
              ·
                refine ⟨1153561447746867517357187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3076163860658313379619165 1153561447746867517357187)
                ·
                  refine ⟨1730342171620301276035781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153561447746867517357187 1730342171620301276035781)
                  ·
                    refine ⟨324439157178806489256709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730342171620301276035781 324439157178806489256709)
                    ·
                      rfl

theorem cell23_1895529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 3, 1, 4].length) (baseStart_1895529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895529 prefixEnd_1895529 := by exact prefixLift 1895529
  have htrace : WordTrace (prefixWord ++ tailWord_1895529) baseStart_1895529 baseEnd_1895529 := by
    simpa [prefixWord, tailWord_1895529, baseEnd_1895529] using wordTrace_append hprefix tailTrace_1895529
  have hstable : (prefixWord ++ tailWord_1895529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895529).length < 2 ^ (prefixWord ++ tailWord_1895529).sum := by decide
  have hdescent : baseEnd_1895529 < baseStart_1895529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895542 : List Nat := [5, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_1895542 : Nat := 118140960795 + 1895542 * 2 ^ 59
def prefixEnd_1895542 : Nat := 4983230072969 + 3 ^ 40 * 1895542 * 2
def baseEnd_1895542 : Nat := 108147127420547546323063

theorem tailTrace_1895542 : CollatzResearch.WordTrace tailWord_1895542 prefixEnd_1895542 108147127420547546323063 := by
  unfold tailWord_1895542
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321006031173908852814055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46090730999188361096683253 4321006031173908852814055)
  ·
    refine ⟨6481509046760863279221083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321006031173908852814055 6481509046760863279221083)
    ·
      refine ⟨9722263570141294918831625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6481509046760863279221083 9722263570141294918831625)
      ·
        refine ⟨7291697677605971189123719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9722263570141294918831625 7291697677605971189123719)
        ·
          refine ⟨10937546516408956783685579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7291697677605971189123719 10937546516408956783685579)
          ·
            refine ⟨16406319774613435175528369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10937546516408956783685579 16406319774613435175528369)
            ·
              refine ⟨12304739830960076381646277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16406319774613435175528369 12304739830960076381646277)
              ·
                refine ⟨2307138718305014321558677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12304739830960076381646277 2307138718305014321558677)
                ·
                  refine ⟨108147127420547546323063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2307138718305014321558677 108147127420547546323063)
                  ·
                    rfl

theorem cell23_1895542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_1895542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895542 prefixEnd_1895542 := by exact prefixLift 1895542
  have htrace : WordTrace (prefixWord ++ tailWord_1895542) baseStart_1895542 baseEnd_1895542 := by
    simpa [prefixWord, tailWord_1895542, baseEnd_1895542] using wordTrace_append hprefix tailTrace_1895542
  have hstable : (prefixWord ++ tailWord_1895542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895542).length < 2 ^ (prefixWord ++ tailWord_1895542).sum := by decide
  have hdescent : baseEnd_1895542 < baseStart_1895542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895555 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 3, 5]
def baseStart_1895555 : Nat := 118140960795 + 1895555 * 2 ^ 59
def prefixEnd_1895555 : Nat := 4983230072969 + 3 ^ 40 * 1895555 * 2
def baseEnd_1895555 : Nat := 324443607344478788681669

theorem tailTrace_1895555 : CollatzResearch.WordTrace tailWord_1895555 prefixEnd_1895555 324443607344478788681669 := by
  unfold tailWord_1895555
  simp only [CollatzResearch.WordTrace]
  refine ⟨69136570647735444865248119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46091047098490296576832079 69136570647735444865248119)
  ·
    refine ⟨103704855971603167297872179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69136570647735444865248119 103704855971603167297872179)
    ·
      refine ⟨155557283957404750946808269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103704855971603167297872179 155557283957404750946808269)
      ·
        refine ⟨58333981484026781605053101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155557283957404750946808269 58333981484026781605053101)
        ·
          refine ⟨21875243056510043101894913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58333981484026781605053101 21875243056510043101894913)
          ·
            refine ⟨16406432292382532326421185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21875243056510043101894913 16406432292382532326421185)
            ·
              refine ⟨12304824219286899244815889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16406432292382532326421185 12304824219286899244815889)
              ·
                refine ⟨9228618164465174433611917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12304824219286899244815889 9228618164465174433611917)
                ·
                  refine ⟨3460731811674440412604469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9228618164465174433611917 3460731811674440412604469)
                  ·
                    refine ⟨324443607344478788681669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3460731811674440412604469 324443607344478788681669)
                    ·
                      rfl

theorem cell23_1895555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 3, 5].length) (baseStart_1895555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895555 prefixEnd_1895555 := by exact prefixLift 1895555
  have htrace : WordTrace (prefixWord ++ tailWord_1895555) baseStart_1895555 baseEnd_1895555 := by
    simpa [prefixWord, tailWord_1895555, baseEnd_1895555] using wordTrace_append hprefix tailTrace_1895555
  have hstable : (prefixWord ++ tailWord_1895555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895555).length < 2 ^ (prefixWord ++ tailWord_1895555).sum := by decide
  have hdescent : baseEnd_1895555 < baseStart_1895555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895589 : List Nat := [1, 3, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_1895589 : Nat := 118140960795 + 1895589 * 2 ^ 59
def prefixEnd_1895589 : Nat := 4983230072969 + 3 ^ 40 * 1895589 * 2
def baseEnd_1895589 : Nat := 324449426791896411006617

theorem tailTrace_1895589 : CollatzResearch.WordTrace tailWord_1895589 prefixEnd_1895589 324449426791896411006617 := by
  unfold tailWord_1895589
  simp only [CollatzResearch.WordTrace]
  refine ⟨69137810729612268671985821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46091873819741512447990547 69137810729612268671985821)
  ·
    refine ⟨25926679023604600751994683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69137810729612268671985821 25926679023604600751994683)
    ·
      refine ⟨38890018535406901127992025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25926679023604600751994683 38890018535406901127992025)
      ·
        refine ⟨29167513901555175845994019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38890018535406901127992025 29167513901555175845994019)
        ·
          refine ⟨43751270852332763768991029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29167513901555175845994019 43751270852332763768991029)
          ·
            refine ⟨4101681642406196603342909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43751270852332763768991029 4101681642406196603342909)
            ·
              refine ⟨1538130615902323726253591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4101681642406196603342909 1538130615902323726253591)
              ·
                refine ⟨2307195923853485589380387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538130615902323726253591 2307195923853485589380387)
                ·
                  refine ⟨3460793885780228384070581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307195923853485589380387 3460793885780228384070581)
                  ·
                    refine ⟨324449426791896411006617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3460793885780228384070581 324449426791896411006617)
                    ·
                      rfl

theorem cell23_1895589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_1895589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895589 prefixEnd_1895589 := by exact prefixLift 1895589
  have htrace : WordTrace (prefixWord ++ tailWord_1895589) baseStart_1895589 baseEnd_1895589 := by
    simpa [prefixWord, tailWord_1895589, baseEnd_1895589] using wordTrace_append hprefix tailTrace_1895589
  have hstable : (prefixWord ++ tailWord_1895589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895589).length < 2 ^ (prefixWord ++ tailWord_1895589).sum := by decide
  have hdescent : baseEnd_1895589 < baseStart_1895589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895615 : List Nat := [1, 1, 2, 2, 2, 2, 5, 8]
def baseStart_1895615 : Nat := 118140960795 + 1895615 * 2 ^ 59
def prefixEnd_1895615 : Nat := 4983230072969 + 3 ^ 40 * 1895615 * 2
def baseEnd_1895615 : Nat := 36050430773063190047953

theorem tailTrace_1895615 : CollatzResearch.WordTrace tailWord_1895615 prefixEnd_1895615 36050430773063190047953 := by
  unfold tailWord_1895615
  simp only [CollatzResearch.WordTrace]
  refine ⟨69138759027518075112432299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46092506018345383408288199 69138759027518075112432299)
  ·
    refine ⟨103708138541277112668648449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69138759027518075112432299 103708138541277112668648449)
    ·
      refine ⟨77781103905957834501486337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103708138541277112668648449 77781103905957834501486337)
      ·
        refine ⟨58335827929468375876114753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77781103905957834501486337 58335827929468375876114753)
        ·
          refine ⟨43751870947101281907086065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58335827929468375876114753 43751870947101281907086065)
          ·
            refine ⟨32813903210325961430314549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43751870947101281907086065 32813903210325961430314549)
            ·
              refine ⟨3076303425968058884091989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32813903210325961430314549 3076303425968058884091989)
              ·
                refine ⟨36050430773063190047953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3076303425968058884091989 36050430773063190047953)
                ·
                  rfl

theorem cell23_1895615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 8].length) (baseStart_1895615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895615 prefixEnd_1895615 := by exact prefixLift 1895615
  have htrace : WordTrace (prefixWord ++ tailWord_1895615) baseStart_1895615 baseEnd_1895615 := by
    simpa [prefixWord, tailWord_1895615, baseEnd_1895615] using wordTrace_append hprefix tailTrace_1895615
  have hstable : (prefixWord ++ tailWord_1895615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895615).length < 2 ^ (prefixWord ++ tailWord_1895615).sum := by decide
  have hdescent : baseEnd_1895615 < baseStart_1895615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895626 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2]
def baseStart_1895626 : Nat := 118140960795 + 1895626 * 2 ^ 59
def prefixEnd_1895626 : Nat := 4983230072969 + 3 ^ 40 * 1895626 * 2
def baseEnd_1895626 : Nat := 973367279159905588257181

theorem tailTrace_1895626 : CollatzResearch.WordTrace tailWord_1895626 prefixEnd_1895626 973367279159905588257181 := by
  unfold tailWord_1895626
  simp only [CollatzResearch.WordTrace]
  refine ⟨17284790057619555997770683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46092773486985482660721821 17284790057619555997770683)
  ·
    refine ⟨25927185086429333996656025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17284790057619555997770683 25927185086429333996656025)
    ·
      refine ⟨19445388814822000497492019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25927185086429333996656025 19445388814822000497492019)
      ·
        refine ⟨29168083222233000746238029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19445388814822000497492019 29168083222233000746238029)
        ·
          refine ⟨10938031208337375279839261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29168083222233000746238029 10938031208337375279839261)
          ·
            refine ⟨4101761703126515729939723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10938031208337375279839261 4101761703126515729939723)
            ·
              refine ⟨6152642554689773594909585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101761703126515729939723 6152642554689773594909585)
              ·
                refine ⟨4614481916017330196182189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6152642554689773594909585 4614481916017330196182189)
                ·
                  refine ⟨1730430718506498823568321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4614481916017330196182189 1730430718506498823568321)
                  ·
                    refine ⟨1297823038879874117676241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1730430718506498823568321 1297823038879874117676241)
                    ·
                      refine ⟨973367279159905588257181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297823038879874117676241 973367279159905588257181)
                      ·
                        rfl

theorem cell23_1895626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_1895626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895626 prefixEnd_1895626 := by exact prefixLift 1895626
  have htrace : WordTrace (prefixWord ++ tailWord_1895626) baseStart_1895626 baseEnd_1895626 := by
    simpa [prefixWord, tailWord_1895626, baseEnd_1895626] using wordTrace_append hprefix tailTrace_1895626
  have hstable : (prefixWord ++ tailWord_1895626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895626).length < 2 ^ (prefixWord ++ tailWord_1895626).sum := by decide
  have hdescent : baseEnd_1895626 < baseStart_1895626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895653 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 2, 4]
def baseStart_1895653 : Nat := 118140960795 + 1895653 * 2 ^ 59
def prefixEnd_1895653 : Nat := 4983230072969 + 3 ^ 40 * 1895653 * 2
def baseEnd_1895653 : Nat := 324460381045858994206519

theorem tailTrace_1895653 : CollatzResearch.WordTrace tailWord_1895653 prefixEnd_1895653 324460381045858994206519 := by
  unfold tailWord_1895653
  simp only [CollatzResearch.WordTrace]
  refine ⟨69140145001380407602315613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46093430000920271734877075 69140145001380407602315613)
  ·
    refine ⟨25927554375517652850868355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69140145001380407602315613 25927554375517652850868355)
    ·
      refine ⟨38891331563276479276302533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25927554375517652850868355 38891331563276479276302533)
      ·
        refine ⟨7292124668114339864306725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38891331563276479276302533 7292124668114339864306725)
        ·
          refine ⟨1367273375271438724557511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7292124668114339864306725 1367273375271438724557511)
          ·
            refine ⟨2050910062907158086836267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367273375271438724557511 2050910062907158086836267)
            ·
              refine ⟨3076365094360737130254401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050910062907158086836267 3076365094360737130254401)
              ·
                refine ⟨2307273820770552847690801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076365094360737130254401 2307273820770552847690801)
                ·
                  refine ⟨1730455365577914635768101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307273820770552847690801 1730455365577914635768101)
                  ·
                    refine ⟨324460381045858994206519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730455365577914635768101 324460381045858994206519)
                    ·
                      rfl

theorem cell23_1895653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 2, 4].length) (baseStart_1895653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895653 prefixEnd_1895653 := by exact prefixLift 1895653
  have htrace : WordTrace (prefixWord ++ tailWord_1895653) baseStart_1895653 baseEnd_1895653 := by
    simpa [prefixWord, tailWord_1895653, baseEnd_1895653] using wordTrace_append hprefix tailTrace_1895653
  have hstable : (prefixWord ++ tailWord_1895653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895653).length < 2 ^ (prefixWord ++ tailWord_1895653).sum := by decide
  have hdescent : baseEnd_1895653 < baseStart_1895653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895659 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 3]
def baseStart_1895659 : Nat := 118140960795 + 1895659 * 2 ^ 59
def prefixEnd_1895659 : Nat := 4983230072969 + 3 ^ 40 * 1895659 * 2
def baseEnd_1895659 : Nat := 973384224021503959144529

theorem tailTrace_1895659 : CollatzResearch.WordTrace tailWord_1895659 prefixEnd_1895659 973384224021503959144529 := by
  unfold tailWord_1895659
  simp only [CollatzResearch.WordTrace]
  refine ⟨69140363839358670627034031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46093575892905780418022687 69140363839358670627034031)
  ·
    refine ⟨103710545759038005940551047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69140363839358670627034031 103710545759038005940551047)
    ·
      refine ⟨155565818638557008910826571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103710545759038005940551047 155565818638557008910826571)
      ·
        refine ⟨233348727957835513366239857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155565818638557008910826571 233348727957835513366239857)
        ·
          refine ⟨175011545968376635024679893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233348727957835513366239857 175011545968376635024679893)
          ·
            refine ⟨4101833108633827383390935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175011545968376635024679893 4101833108633827383390935)
            ·
              refine ⟨6152749662950741075086403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101833108633827383390935 6152749662950741075086403)
              ·
                refine ⟨9229124494426111612629605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6152749662950741075086403 9229124494426111612629605)
                ·
                  refine ⟨1730460842704895927368051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9229124494426111612629605 1730460842704895927368051)
                  ·
                    refine ⟨2595691264057343891052077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730460842704895927368051 2595691264057343891052077)
                    ·
                      refine ⟨973384224021503959144529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595691264057343891052077 973384224021503959144529)
                      ·
                        rfl

theorem cell23_1895659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 3].length) (baseStart_1895659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895659 prefixEnd_1895659 := by exact prefixLift 1895659
  have htrace : WordTrace (prefixWord ++ tailWord_1895659) baseStart_1895659 baseEnd_1895659 := by
    simpa [prefixWord, tailWord_1895659, baseEnd_1895659] using wordTrace_append hprefix tailTrace_1895659
  have hstable : (prefixWord ++ tailWord_1895659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895659).length < 2 ^ (prefixWord ++ tailWord_1895659).sum := by decide
  have hdescent : baseEnd_1895659 < baseStart_1895659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895676 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 1, 3, 3]
def baseStart_1895676 : Nat := 118140960795 + 1895676 * 2 ^ 59
def prefixEnd_1895676 : Nat := 4983230072969 + 3 ^ 40 * 1895676 * 2
def baseEnd_1895676 : Nat := 973392953192630392631951

theorem tailTrace_1895676 : CollatzResearch.WordTrace tailWord_1895676 prefixEnd_1895676 973392953192630392631951 := by
  unfold tailWord_1895676
  simp only [CollatzResearch.WordTrace]
  refine ⟨34570491940148541265201441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46093989253531388353601921 34570491940148541265201441)
  ·
    refine ⟨25927868955111405948901081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34570491940148541265201441 25927868955111405948901081)
    ·
      refine ⟨19445901716333554461675811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25927868955111405948901081 19445901716333554461675811)
      ·
        refine ⟨29168852574500331692513717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19445901716333554461675811 29168852574500331692513717)
        ·
          refine ⟨2734579928859406096173161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29168852574500331692513717 2734579928859406096173161)
          ·
            refine ⟨2050934946644554572129871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2734579928859406096173161 2050934946644554572129871)
            ·
              refine ⟨3076402419966831858194807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2050934946644554572129871 3076402419966831858194807)
              ·
                refine ⟨4614603629950247787292211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3076402419966831858194807 4614603629950247787292211)
                ·
                  refine ⟨6921905444925371680938317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4614603629950247787292211 6921905444925371680938317)
                  ·
                    refine ⟨2595714541847014380351869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6921905444925371680938317 2595714541847014380351869)
                    ·
                      refine ⟨973392953192630392631951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2595714541847014380351869 973392953192630392631951)
                      ·
                        rfl

theorem cell23_1895676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_1895676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895676 prefixEnd_1895676 := by exact prefixLift 1895676
  have htrace : WordTrace (prefixWord ++ tailWord_1895676) baseStart_1895676 baseEnd_1895676 := by
    simpa [prefixWord, tailWord_1895676, baseEnd_1895676] using wordTrace_append hprefix tailTrace_1895676
  have hstable : (prefixWord ++ tailWord_1895676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895676).length < 2 ^ (prefixWord ++ tailWord_1895676).sum := by decide
  have hdescent : baseEnd_1895676 < baseStart_1895676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895716 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_1895716 : Nat := 118140960795 + 1895716 * 2 ^ 59
def prefixEnd_1895716 : Nat := 4983230072969 + 3 ^ 40 * 1895716 * 2
def baseEnd_1895716 : Nat := 973413492418810236131767

theorem tailTrace_1895716 : CollatzResearch.WordTrace tailWord_1895716 prefixEnd_1895716 973413492418810236131767 := by
  unfold tailWord_1895716
  simp only [CollatzResearch.WordTrace]
  refine ⟨34571221400076084680929501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46094961866768112907906001 34571221400076084680929501)
  ·
    refine ⟨12964208025028531755348563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34571221400076084680929501 12964208025028531755348563)
    ·
      refine ⟨19446312037542797633022845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12964208025028531755348563 19446312037542797633022845)
      ·
        refine ⟨7292367014078549112383567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19446312037542797633022845 7292367014078549112383567)
        ·
          refine ⟨10938550521117823668575351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7292367014078549112383567 10938550521117823668575351)
          ·
            refine ⟨16407825781676735502863027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10938550521117823668575351 16407825781676735502863027)
            ·
              refine ⟨24611738672515103254294541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16407825781676735502863027 24611738672515103254294541)
              ·
                refine ⟨9229402002193163720360453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24611738672515103254294541 9229402002193163720360453)
                ·
                  refine ⟨1730512875411218197567585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9229402002193163720360453 1730512875411218197567585)
                  ·
                    refine ⟨1297884656558413648175689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1730512875411218197567585 1297884656558413648175689)
                    ·
                      refine ⟨973413492418810236131767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297884656558413648175689 973413492418810236131767)
                      ·
                        rfl

theorem cell23_1895716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_1895716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895716 prefixEnd_1895716 := by exact prefixLift 1895716
  have htrace : WordTrace (prefixWord ++ tailWord_1895716) baseStart_1895716 baseEnd_1895716 := by
    simpa [prefixWord, tailWord_1895716, baseEnd_1895716] using wordTrace_append hprefix tailTrace_1895716
  have hstable : (prefixWord ++ tailWord_1895716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895716).length < 2 ^ (prefixWord ++ tailWord_1895716).sum := by decide
  have hdescent : baseEnd_1895716 < baseStart_1895716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895733 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_1895733 : Nat := 118140960795 + 1895733 * 2 ^ 59
def prefixEnd_1895733 : Nat := 4983230072969 + 3 ^ 40 * 1895733 * 2
def baseEnd_1895733 : Nat := 973422221589936669619189

theorem tailTrace_1895733 : CollatzResearch.WordTrace tailWord_1895733 prefixEnd_1895733 973422221589936669619189 := by
  unfold tailWord_1895733
  simp only [CollatzResearch.WordTrace]
  refine ⟨69143062841090581265227853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46095375227393720843485235 69143062841090581265227853)
  ·
    refine ⟨25928648565408967974460445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69143062841090581265227853 25928648565408967974460445)
    ·
      refine ⟨9723243212028362990422667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25928648565408967974460445 9723243212028362990422667)
      ·
        refine ⟨14584864818042544485634001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9723243212028362990422667 14584864818042544485634001)
        ·
          refine ⟨10938648613531908364225501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14584864818042544485634001 10938648613531908364225501)
          ·
            refine ⟨4101993230074465636584563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10938648613531908364225501 4101993230074465636584563)
            ·
              refine ⟨6152989845111698454876845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4101993230074465636584563 6152989845111698454876845)
              ·
                refine ⟨2307371191916886920578817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6152989845111698454876845 2307371191916886920578817)
                ·
                  refine ⟨1730528393937665190434113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307371191916886920578817 1730528393937665190434113)
                  ·
                    refine ⟨1297896295453248892825585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1730528393937665190434113 1297896295453248892825585)
                    ·
                      refine ⟨973422221589936669619189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1297896295453248892825585 973422221589936669619189)
                      ·
                        rfl

theorem cell23_1895733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_1895733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895733 prefixEnd_1895733 := by exact prefixLift 1895733
  have htrace : WordTrace (prefixWord ++ tailWord_1895733) baseStart_1895733 baseEnd_1895733 := by
    simpa [prefixWord, tailWord_1895733, baseEnd_1895733] using wordTrace_append hprefix tailTrace_1895733
  have hstable : (prefixWord ++ tailWord_1895733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895733).length < 2 ^ (prefixWord ++ tailWord_1895733).sum := by decide
  have hdescent : baseEnd_1895733 < baseStart_1895733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895799 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 3, 4]
def baseStart_1895799 : Nat := 118140960795 + 1895799 * 2 ^ 59
def prefixEnd_1895799 : Nat := 4983230072969 + 3 ^ 40 * 1895799 * 2
def baseEnd_1895799 : Nat := 324485370437711137131295

theorem tailTrace_1895799 : CollatzResearch.WordTrace tailWord_1895799 prefixEnd_1895799 324485370437711137131295 := by
  unfold tailWord_1895799
  simp only [CollatzResearch.WordTrace]
  refine ⟨69145470058851474537130451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46096980039234316358086967 69145470058851474537130451)
  ·
    refine ⟨103718205088277211805695677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69145470058851474537130451 103718205088277211805695677)
    ·
      refine ⟨38894326908103954427135879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103718205088277211805695677 38894326908103954427135879)
      ·
        refine ⟨58341490362155931640703819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38894326908103954427135879 58341490362155931640703819)
        ·
          refine ⟨87512235543233897461055729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58341490362155931640703819 87512235543233897461055729)
          ·
            refine ⟨65634176657425423095791797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87512235543233897461055729 65634176657425423095791797)
            ·
              refine ⟨6153204061633633415230481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65634176657425423095791797 6153204061633633415230481)
              ·
                refine ⟨4614903046225225061422861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6153204061633633415230481 4614903046225225061422861)
                ·
                  refine ⟨1730588642334459398033573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4614903046225225061422861 1730588642334459398033573)
                  ·
                    refine ⟨324485370437711137131295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730588642334459398033573 324485370437711137131295)
                    ·
                      rfl

theorem cell23_1895799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 3, 4].length) (baseStart_1895799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895799 prefixEnd_1895799 := by exact prefixLift 1895799
  have htrace : WordTrace (prefixWord ++ tailWord_1895799) baseStart_1895799 baseEnd_1895799 := by
    simpa [prefixWord, tailWord_1895799, baseEnd_1895799] using wordTrace_append hprefix tailTrace_1895799
  have hstable : (prefixWord ++ tailWord_1895799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895799).length < 2 ^ (prefixWord ++ tailWord_1895799).sum := by decide
  have hdescent : baseEnd_1895799 < baseStart_1895799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895802 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4]
def baseStart_1895802 : Nat := 118140960795 + 1895802 * 2 ^ 59
def prefixEnd_1895802 : Nat := 4983230072969 + 3 ^ 40 * 1895802 * 2
def baseEnd_1895802 : Nat := 973457651755096899656371

theorem tailTrace_1895802 : CollatzResearch.WordTrace tailWord_1895802 prefixEnd_1895802 973457651755096899656371 := by
  unfold tailWord_1895802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17286394869460151512372415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46097052985227070699659773 17286394869460151512372415)
  ·
    refine ⟨25929592304190227268558623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17286394869460151512372415 25929592304190227268558623)
    ·
      refine ⟨38894388456285340902837935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25929592304190227268558623 38894388456285340902837935)
      ·
        refine ⟨58341582684428011354256903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38894388456285340902837935 58341582684428011354256903)
        ·
          refine ⟨87512374026642017031385355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58341582684428011354256903 87512374026642017031385355)
          ·
            refine ⟨131268561039963025547078033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87512374026642017031385355 131268561039963025547078033)
            ·
              refine ⟨98451420779972269160308525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131268561039963025547078033 98451420779972269160308525)
              ·
                refine ⟨36919282792489600935115697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98451420779972269160308525 36919282792489600935115697)
                ·
                  refine ⟨27689462094367200701336773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36919282792489600935115697 27689462094367200701336773)
                  ·
                    refine ⟨5191774142693850131500645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27689462094367200701336773 5191774142693850131500645)
                    ·
                      refine ⟨973457651755096899656371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5191774142693850131500645 973457651755096899656371)
                      ·
                        rfl

theorem cell23_1895802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_1895802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895802 prefixEnd_1895802 := by exact prefixLift 1895802
  have htrace : WordTrace (prefixWord ++ tailWord_1895802) baseStart_1895802 baseEnd_1895802 := by
    simpa [prefixWord, tailWord_1895802, baseEnd_1895802] using wordTrace_append hprefix tailTrace_1895802
  have hstable : (prefixWord ++ tailWord_1895802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895802).length < 2 ^ (prefixWord ++ tailWord_1895802).sum := by decide
  have hdescent : baseEnd_1895802 < baseStart_1895802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895829 : List Nat := [1, 3, 2, 1, 1, 2, 5, 2, 6]
def baseStart_1895829 : Nat := 118140960795 + 1895829 * 2 ^ 59
def prefixEnd_1895829 : Nat := 4983230072969 + 3 ^ 40 * 1895829 * 2
def baseEnd_1895829 : Nat := 108163501748085366002083

theorem tailTrace_1895829 : CollatzResearch.WordTrace tailWord_1895829 prefixEnd_1895829 108163501748085366002083 := by
  unfold tailWord_1895829
  simp only [CollatzResearch.WordTrace]
  refine ⟨69146564248742789660722541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46097709499161859773815027 69146564248742789660722541)
  ·
    refine ⟨25929961593278546122770953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69146564248742789660722541 25929961593278546122770953)
    ·
      refine ⟨19447471194958909592078215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25929961593278546122770953 19447471194958909592078215)
      ·
        refine ⟨29171206792438364388117323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19447471194958909592078215 29171206792438364388117323)
        ·
          refine ⟨43756810188657546582175985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29171206792438364388117323 43756810188657546582175985)
          ·
            refine ⟨32817607641493159936631989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43756810188657546582175985 32817607641493159936631989)
            ·
              refine ⟨3076650716389983744059249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32817607641493159936631989 3076650716389983744059249)
              ·
                refine ⟨2307488037292487808044437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076650716389983744059249 2307488037292487808044437)
                ·
                  refine ⟨108163501748085366002083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2307488037292487808044437 108163501748085366002083)
                  ·
                    rfl

theorem cell23_1895829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_1895829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895829 prefixEnd_1895829 := by exact prefixLift 1895829
  have htrace : WordTrace (prefixWord ++ tailWord_1895829) baseStart_1895829 baseEnd_1895829 := by
    simpa [prefixWord, tailWord_1895829, baseEnd_1895829] using wordTrace_append hprefix tailTrace_1895829
  have hstable : (prefixWord ++ tailWord_1895829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895829).length < 2 ^ (prefixWord ++ tailWord_1895829).sum := by decide
  have hdescent : baseEnd_1895829 < baseStart_1895829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895852 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 7]
def baseStart_1895852 : Nat := 118140960795 + 1895852 * 2 ^ 59
def prefixEnd_1895852 : Nat := 4983230072969 + 3 ^ 40 * 1895852 * 2
def baseEnd_1895852 : Nat := 973483325787821704031141

theorem tailTrace_1895852 : CollatzResearch.WordTrace tailWord_1895852 prefixEnd_1895852 973483325787821704031141 := by
  unfold tailWord_1895852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34573701563829732294404905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46098268751772976392539873 34573701563829732294404905)
  ·
    refine ⟨25930276172872299220803679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34573701563829732294404905 25930276172872299220803679)
    ·
      refine ⟨38895414259308448831205519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25930276172872299220803679 38895414259308448831205519)
      ·
        refine ⟨58343121388962673246808279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38895414259308448831205519 58343121388962673246808279)
        ·
          refine ⟨87514682083444009870212419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58343121388962673246808279 87514682083444009870212419)
          ·
            refine ⟨131272023125166014805318629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87514682083444009870212419 131272023125166014805318629)
            ·
              refine ⟨24613504335968627775997243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 131272023125166014805318629 24613504335968627775997243)
              ·
                refine ⟨36920256503952941663995865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24613504335968627775997243 36920256503952941663995865)
                ·
                  refine ⟨27690192377964706247996899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36920256503952941663995865 27690192377964706247996899)
                  ·
                    refine ⟨41535288566947059371995349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27690192377964706247996899 41535288566947059371995349)
                    ·
                      refine ⟨973483325787821704031141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41535288566947059371995349 973483325787821704031141)
                      ·
                        rfl

theorem cell23_1895852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_1895852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895852 prefixEnd_1895852 := by exact prefixLift 1895852
  have htrace : WordTrace (prefixWord ++ tailWord_1895852) baseStart_1895852 baseEnd_1895852 := by
    simpa [prefixWord, tailWord_1895852, baseEnd_1895852] using wordTrace_append hprefix tailTrace_1895852
  have hstable : (prefixWord ++ tailWord_1895852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895852).length < 2 ^ (prefixWord ++ tailWord_1895852).sum := by decide
  have hdescent : baseEnd_1895852 < baseStart_1895852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895899 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 3]
def baseStart_1895899 : Nat := 118140960795 + 1895899 * 2 ^ 59
def prefixEnd_1895899 : Nat := 4983230072969 + 3 ^ 40 * 1895899 * 2
def baseEnd_1895899 : Nat := 973507459378583020143425

theorem tailTrace_1895899 : CollatzResearch.WordTrace tailWord_1895899 prefixEnd_1895899 973507459378583020143425 := by
  unfold tailWord_1895899
  simp only [CollatzResearch.WordTrace]
  refine ⟨69149117358489191615770751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46099411572326127743847167 69149117358489191615770751)
  ·
    refine ⟨103723676037733787423656127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69149117358489191615770751 103723676037733787423656127)
    ·
      refine ⟨155585514056600681135484191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103723676037733787423656127 155585514056600681135484191)
      ·
        refine ⟨233378271084901021703226287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155585514056600681135484191 233378271084901021703226287)
        ·
          refine ⟨350067406627351532554839431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233378271084901021703226287 350067406627351532554839431)
          ·
            refine ⟨525101109941027298832259147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 350067406627351532554839431 525101109941027298832259147)
            ·
              refine ⟨787651664911540948248388721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 525101109941027298832259147 787651664911540948248388721)
              ·
                refine ⟨590738748683655711186291541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 787651664911540948248388721 590738748683655711186291541)
                ·
                  refine ⟨3461359855568295182732177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 590738748683655711186291541 3461359855568295182732177)
                  ·
                    refine ⟨2596019891676221387049133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461359855568295182732177 2596019891676221387049133)
                    ·
                      refine ⟨973507459378583020143425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596019891676221387049133 973507459378583020143425)
                      ·
                        rfl

theorem cell23_1895899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 3].length) (baseStart_1895899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895899 prefixEnd_1895899 := by exact prefixLift 1895899
  have htrace : WordTrace (prefixWord ++ tailWord_1895899) baseStart_1895899 baseEnd_1895899 := by
    simpa [prefixWord, tailWord_1895899, baseEnd_1895899] using wordTrace_append hprefix tailTrace_1895899
  have hstable : (prefixWord ++ tailWord_1895899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895899).length < 2 ^ (prefixWord ++ tailWord_1895899).sum := by decide
  have hdescent : baseEnd_1895899 < baseStart_1895899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895916 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 3]
def baseStart_1895916 : Nat := 118140960795 + 1895916 * 2 ^ 59
def prefixEnd_1895916 : Nat := 4983230072969 + 3 ^ 40 * 1895916 * 2
def baseEnd_1895916 : Nat := 973516188549709453630847

theorem tailTrace_1895916 : CollatzResearch.WordTrace tailWord_1895916 prefixEnd_1895916 973516188549709453630847 := by
  unfold tailWord_1895916
  simp only [CollatzResearch.WordTrace]
  refine ⟨34574868699713801759569801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46099824932951735679426401 34574868699713801759569801)
  ·
    refine ⟨25931151524785351319677351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34574868699713801759569801 25931151524785351319677351)
    ·
      refine ⟨38896727287178026979516027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25931151524785351319677351 38896727287178026979516027)
      ·
        refine ⟨58345090930767040469274041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38896727287178026979516027 58345090930767040469274041)
        ·
          refine ⟨43758818198075280351955531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58345090930767040469274041 43758818198075280351955531)
          ·
            refine ⟨65638227297112920527933297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43758818198075280351955531 65638227297112920527933297)
            ·
              refine ⟨49228670472834690395949973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65638227297112920527933297 49228670472834690395949973)
              ·
                refine ⟨2307593928414126112310155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49228670472834690395949973 2307593928414126112310155)
                ·
                  refine ⟨3461390892621189168465233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307593928414126112310155 3461390892621189168465233)
                  ·
                    refine ⟨2596043169465891876348925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461390892621189168465233 2596043169465891876348925)
                    ·
                      refine ⟨973516188549709453630847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596043169465891876348925 973516188549709453630847)
                      ·
                        rfl

theorem cell23_1895916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 3].length) (baseStart_1895916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895916 prefixEnd_1895916 := by exact prefixLift 1895916
  have htrace : WordTrace (prefixWord ++ tailWord_1895916) baseStart_1895916 baseEnd_1895916 := by
    simpa [prefixWord, tailWord_1895916, baseEnd_1895916] using wordTrace_append hprefix tailTrace_1895916
  have hstable : (prefixWord ++ tailWord_1895916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895916).length < 2 ^ (prefixWord ++ tailWord_1895916).sum := by decide
  have hdescent : baseEnd_1895916 < baseStart_1895916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895926 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1895926 : Nat := 118140960795 + 1895926 * 2 ^ 59
def prefixEnd_1895926 : Nat := 4983230072969 + 3 ^ 40 * 1895926 * 2
def baseEnd_1895926 : Nat := 973521323356254414505801

theorem tailTrace_1895926 : CollatzResearch.WordTrace tailWord_1895926 prefixEnd_1895926 973521323356254414505801 := by
  unfold tailWord_1895926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321881383086960951687727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46100068086260916818002421 4321881383086960951687727)
  ·
    refine ⟨6482822074630441427531591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4321881383086960951687727 6482822074630441427531591)
    ·
      refine ⟨9724233111945662141297387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6482822074630441427531591 9724233111945662141297387)
      ·
        refine ⟨14586349667918493211946081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9724233111945662141297387 14586349667918493211946081)
        ·
          refine ⟨10939762250938869908959561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14586349667918493211946081 10939762250938869908959561)
          ·
            refine ⟨8204821688204152431719671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10939762250938869908959561 8204821688204152431719671)
            ·
              refine ⟨12307232532306228647579507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8204821688204152431719671 12307232532306228647579507)
              ·
                refine ⟨18460848798459342971369261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12307232532306228647579507 18460848798459342971369261)
                ·
                  refine ⟨6922818299422253614263473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18460848798459342971369261 6922818299422253614263473)
                  ·
                    refine ⟨5192113724566690210697605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6922818299422253614263473 5192113724566690210697605)
                    ·
                      refine ⟨973521323356254414505801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5192113724566690210697605 973521323356254414505801)
                      ·
                        rfl

theorem cell23_1895926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1895926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895926 prefixEnd_1895926 := by exact prefixLift 1895926
  have htrace : WordTrace (prefixWord ++ tailWord_1895926) baseStart_1895926 baseEnd_1895926 := by
    simpa [prefixWord, tailWord_1895926, baseEnd_1895926] using wordTrace_append hprefix tailTrace_1895926
  have hstable : (prefixWord ++ tailWord_1895926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895926).length < 2 ^ (prefixWord ++ tailWord_1895926).sum := by decide
  have hdescent : baseEnd_1895926 < baseStart_1895926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895930 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2]
def baseStart_1895930 : Nat := 118140960795 + 1895930 * 2 ^ 59
def prefixEnd_1895930 : Nat := 4983230072969 + 3 ^ 40 * 1895930 * 2
def baseEnd_1895930 : Nat := 973523377278872398855783

theorem tailTrace_1895930 : CollatzResearch.WordTrace tailWord_1895930 prefixEnd_1895930 973523377278872398855783 := by
  unfold tailWord_1895930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17287562005344220977537311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46100165347584589273432829 17287562005344220977537311)
  ·
    refine ⟨25931343008016331466305967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17287562005344220977537311 25931343008016331466305967)
    ·
      refine ⟨38897014512024497199458951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25931343008016331466305967 38897014512024497199458951)
      ·
        refine ⟨58345521768036745799188427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38897014512024497199458951 58345521768036745799188427)
        ·
          refine ⟨87518282652055118698782641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58345521768036745799188427 87518282652055118698782641)
          ·
            refine ⟨65638711989041339024086981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87518282652055118698782641 65638711989041339024086981)
            ·
              refine ⟨12307258497945251067016309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65638711989041339024086981 12307258497945251067016309)
              ·
                refine ⟨1153805484182367287532779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12307258497945251067016309 1153805484182367287532779)
                ·
                  refine ⟨1730708226273550931299169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153805484182367287532779 1730708226273550931299169)
                  ·
                    refine ⟨1298031169705163198474377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1730708226273550931299169 1298031169705163198474377)
                    ·
                      refine ⟨973523377278872398855783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298031169705163198474377 973523377278872398855783)
                      ·
                        rfl

theorem cell23_1895930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 1, 2, 2].length) (baseStart_1895930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895930 prefixEnd_1895930 := by exact prefixLift 1895930
  have htrace : WordTrace (prefixWord ++ tailWord_1895930) baseStart_1895930 baseEnd_1895930 := by
    simpa [prefixWord, tailWord_1895930, baseEnd_1895930] using wordTrace_append hprefix tailTrace_1895930
  have hstable : (prefixWord ++ tailWord_1895930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895930).length < 2 ^ (prefixWord ++ tailWord_1895930).sum := by decide
  have hdescent : baseEnd_1895930 < baseStart_1895930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895940 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1895940 : Nat := 118140960795 + 1895940 * 2 ^ 59
def prefixEnd_1895940 : Nat := 4983230072969 + 3 ^ 40 * 1895940 * 2
def baseEnd_1895940 : Nat := 324509504028472453243579

theorem tailTrace_1895940 : CollatzResearch.WordTrace tailWord_1895940 prefixEnd_1895940 324509504028472453243579 := by
  unfold tailWord_1895940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34575306375670327809006637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46100408500893770412008849 34575306375670327809006637)
  ·
    refine ⟨12965739890876372928377489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34575306375670327809006637 12965739890876372928377489)
    ·
      refine ⟨9724304918157279696283117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12965739890876372928377489 9724304918157279696283117)
      ·
        refine ⟨3646614344308979886106169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9724304918157279696283117 3646614344308979886106169)
        ·
          refine ⟨2734960758231734914579627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3646614344308979886106169 2734960758231734914579627)
          ·
            refine ⟨4102441137347602371869441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734960758231734914579627 4102441137347602371869441)
            ·
              refine ⟨3076830853010701778902081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4102441137347602371869441 3076830853010701778902081)
              ·
                refine ⟨2307623139758026334176561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076830853010701778902081 2307623139758026334176561)
                ·
                  refine ⟨1730717354818519750632421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307623139758026334176561 1730717354818519750632421)
                  ·
                    refine ⟨324509504028472453243579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730717354818519750632421 324509504028472453243579)
                    ·
                      rfl

theorem cell23_1895940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1895940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895940 prefixEnd_1895940 := by exact prefixLift 1895940
  have htrace : WordTrace (prefixWord ++ tailWord_1895940) baseStart_1895940 baseEnd_1895940 := by
    simpa [prefixWord, tailWord_1895940, baseEnd_1895940] using wordTrace_append hprefix tailTrace_1895940
  have hstable : (prefixWord ++ tailWord_1895940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895940).length < 2 ^ (prefixWord ++ tailWord_1895940).sum := by decide
  have hdescent : baseEnd_1895940 < baseStart_1895940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895947 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 1, 2, 2]
def baseStart_1895947 : Nat := 118140960795 + 1895947 * 2 ^ 59
def prefixEnd_1895947 : Nat := 4983230072969 + 3 ^ 40 * 1895947 * 2
def baseEnd_1895947 : Nat := 973532106449998832343205

theorem tailTrace_1895947 : CollatzResearch.WordTrace tailWord_1895947 prefixEnd_1895947 973532106449998832343205 := by
  unfold tailWord_1895947
  simp only [CollatzResearch.WordTrace]
  refine ⟨69150868062315295813518095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46100578708210197209012063 69150868062315295813518095)
  ·
    refine ⟨103726302093472943720277143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69150868062315295813518095 103726302093472943720277143)
    ·
      refine ⟨155589453140209415580415715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103726302093472943720277143 155589453140209415580415715)
      ·
        refine ⟨233384179710314123370623573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155589453140209415580415715 233384179710314123370623573)
        ·
          refine ⟨2734970855980243633249495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 233384179710314123370623573 2734970855980243633249495)
          ·
            refine ⟨4102456283970365449874243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2734970855980243633249495 4102456283970365449874243)
            ·
              refine ⟨6153684425955548174811365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4102456283970365449874243 6153684425955548174811365)
              ·
                refine ⟨1153815829866665282777131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6153684425955548174811365 1153815829866665282777131)
                ·
                  refine ⟨1730723744799997924165697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153815829866665282777131 1730723744799997924165697)
                  ·
                    refine ⟨1298042808599998443124273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1730723744799997924165697 1298042808599998443124273)
                    ·
                      refine ⟨973532106449998832343205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298042808599998443124273 973532106449998832343205)
                      ·
                        rfl

theorem cell23_1895947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 1, 2, 2].length) (baseStart_1895947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895947 prefixEnd_1895947 := by exact prefixLift 1895947
  have htrace : WordTrace (prefixWord ++ tailWord_1895947) baseStart_1895947 baseEnd_1895947 := by
    simpa [prefixWord, tailWord_1895947, baseEnd_1895947] using wordTrace_append hprefix tailTrace_1895947
  have hstable : (prefixWord ++ tailWord_1895947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895947).length < 2 ^ (prefixWord ++ tailWord_1895947).sum := by decide
  have hdescent : baseEnd_1895947 < baseStart_1895947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895973 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 1, 3, 2]
def baseStart_1895973 : Nat := 118140960795 + 1895973 * 2 ^ 59
def prefixEnd_1895973 : Nat := 4983230072969 + 3 ^ 40 * 1895973 * 2
def baseEnd_1895973 : Nat := 973545456947015730618085

theorem tailTrace_1895973 : CollatzResearch.WordTrace tailWord_1895973 prefixEnd_1895973 973545456947015730618085 := by
  unfold tailWord_1895973
  simp only [CollatzResearch.WordTrace]
  refine ⟨69151816360221102253964573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46101210906814068169309715 69151816360221102253964573)
  ·
    refine ⟨25931931135082913345236715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69151816360221102253964573 25931931135082913345236715)
    ·
      refine ⟨38897896702624370017855073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25931931135082913345236715 38897896702624370017855073)
      ·
        refine ⟨29173422526968277513391305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38897896702624370017855073 29173422526968277513391305)
        ·
          refine ⟨21880066895226208135043479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29173422526968277513391305 21880066895226208135043479)
          ·
            refine ⟨32820100342839312202565219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21880066895226208135043479 32820100342839312202565219)
            ·
              refine ⟨49230150514258968303847829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32820100342839312202565219 49230150514258968303847829)
              ·
                refine ⟨2307663305355889139242867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49230150514258968303847829 2307663305355889139242867)
                ·
                  refine ⟨3461494958033833708864301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307663305355889139242867 3461494958033833708864301)
                  ·
                    refine ⟨1298060609262687640824113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461494958033833708864301 1298060609262687640824113)
                    ·
                      refine ⟨973545456947015730618085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298060609262687640824113 973545456947015730618085)
                      ·
                        rfl

theorem cell23_1895973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_1895973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895973 prefixEnd_1895973 := by exact prefixLift 1895973
  have htrace : WordTrace (prefixWord ++ tailWord_1895973) baseStart_1895973 baseEnd_1895973 := by
    simpa [prefixWord, tailWord_1895973, baseEnd_1895973] using wordTrace_append hprefix tailTrace_1895973
  have hstable : (prefixWord ++ tailWord_1895973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895973).length < 2 ^ (prefixWord ++ tailWord_1895973).sum := by decide
  have hdescent : baseEnd_1895973 < baseStart_1895973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1895997 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1895997 : Nat := 118140960795 + 1895997 * 2 ^ 59
def prefixEnd_1895997 : Nat := 4983230072969 + 3 ^ 40 * 1895997 * 2
def baseEnd_1895997 : Nat := 973557780482723636717975

theorem tailTrace_1895997 : CollatzResearch.WordTrace tailWord_1895997 prefixEnd_1895997 973557780482723636717975 := by
  unfold tailWord_1895997
  simp only [CollatzResearch.WordTrace]
  refine ⟨69152691712134154352838245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46101794474756102901892163 69152691712134154352838245)
  ·
    refine ⟨12966129696025153941157171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69152691712134154352838245 12966129696025153941157171)
    ·
      refine ⟨19449194544037730911735757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12966129696025153941157171 19449194544037730911735757)
      ·
        refine ⟨7293447954014149091900909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19449194544037730911735757 7293447954014149091900909)
        ·
          refine ⟨2735042982755305909462841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7293447954014149091900909 2735042982755305909462841)
          ·
            refine ⟨2051282237066479432097131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735042982755305909462841 2051282237066479432097131)
            ·
              refine ⟨3076923355599719148145697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051282237066479432097131 3076923355599719148145697)
              ·
                refine ⟨2307692516699789361109273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3076923355599719148145697 2307692516699789361109273)
                ·
                  refine ⟨1730769387524842020831955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307692516699789361109273 1730769387524842020831955)
                  ·
                    refine ⟨2596154081287263031247933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730769387524842020831955 2596154081287263031247933)
                    ·
                      refine ⟨973557780482723636717975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596154081287263031247933 973557780482723636717975)
                      ·
                        rfl

theorem cell23_1895997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1895997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1895997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1895997 prefixEnd_1895997 := by exact prefixLift 1895997
  have htrace : WordTrace (prefixWord ++ tailWord_1895997) baseStart_1895997 baseEnd_1895997 := by
    simpa [prefixWord, tailWord_1895997, baseEnd_1895997] using wordTrace_append hprefix tailTrace_1895997
  have hstable : (prefixWord ++ tailWord_1895997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1895997).length < 2 ^ (prefixWord ++ tailWord_1895997).sum := by decide
  have hdescent : baseEnd_1895997 < baseStart_1895997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1895997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896049 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_1896049 : Nat := 118140960795 + 1896049 * 2 ^ 59
def prefixEnd_1896049 : Nat := 4983230072969 + 3 ^ 40 * 1896049 * 2
def baseEnd_1896049 : Nat := 973584481476757433267735

theorem tailTrace_1896049 : CollatzResearch.WordTrace tailWord_1896049 prefixEnd_1896049 973584481476757433267735 := by
  unfold tailWord_1896049
  simp only [CollatzResearch.WordTrace]
  refine ⟨69154588307945767233731201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46103058871963844822487467 69154588307945767233731201)
  ·
    refine ⟨51865941230959325425298401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69154588307945767233731201 51865941230959325425298401)
    ·
      refine ⟨38899455923219494068973801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51865941230959325425298401 38899455923219494068973801)
      ·
        refine ⟨29174591942414620551730351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38899455923219494068973801 29174591942414620551730351)
        ·
          refine ⟨43761887913621930827595527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29174591942414620551730351 43761887913621930827595527)
          ·
            refine ⟨65642831870432896241393291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43761887913621930827595527 65642831870432896241393291)
            ·
              refine ⟨98464247805649344362089937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65642831870432896241393291 98464247805649344362089937)
              ·
                refine ⟨73848185854237008271567453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98464247805649344362089937 73848185854237008271567453)
                ·
                  refine ⟨27693069695338878101837795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73848185854237008271567453 27693069695338878101837795)
                  ·
                    refine ⟨41539604543008317152756693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27693069695338878101837795 41539604543008317152756693)
                    ·
                      refine ⟨973584481476757433267735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41539604543008317152756693 973584481476757433267735)
                      ·
                        rfl

theorem cell23_1896049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_1896049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896049 prefixEnd_1896049 := by exact prefixLift 1896049
  have htrace : WordTrace (prefixWord ++ tailWord_1896049) baseStart_1896049 baseEnd_1896049 := by
    simpa [prefixWord, tailWord_1896049, baseEnd_1896049] using wordTrace_append hprefix tailTrace_1896049
  have hstable : (prefixWord ++ tailWord_1896049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896049).length < 2 ^ (prefixWord ++ tailWord_1896049).sum := by decide
  have hdescent : baseEnd_1896049 < baseStart_1896049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896076 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1896076 : Nat := 118140960795 + 1896076 * 2 ^ 59
def prefixEnd_1896076 : Nat := 4983230072969 + 3 ^ 40 * 1896076 * 2
def baseEnd_1896076 : Nat := 973598345454428827630111

theorem tailTrace_1896076 : CollatzResearch.WordTrace tailWord_1896076 prefixEnd_1896076 973598345454428827630111 := by
  unfold tailWord_1896076
  simp only [CollatzResearch.WordTrace]
  refine ⟨34577786539423975422482041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46103715385898633896642721 34577786539423975422482041)
  ·
    refine ⟨25933339904567981566861531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34577786539423975422482041 25933339904567981566861531)
    ·
      refine ⟨38900009856851972350292297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25933339904567981566861531 38900009856851972350292297)
      ·
        refine ⟨29175007392638979262719223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38900009856851972350292297 29175007392638979262719223)
        ·
          refine ⟨43762511088958468894078835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29175007392638979262719223 43762511088958468894078835)
          ·
            refine ⟨65643766633437703341118253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43762511088958468894078835 65643766633437703341118253)
            ·
              refine ⟨24616412487539138752919345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65643766633437703341118253 24616412487539138752919345)
              ·
                refine ⟨18462309365654354064689509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24616412487539138752919345 18462309365654354064689509)
                ·
                  refine ⟨3461683006060191387129283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18462309365654354064689509 3461683006060191387129283)
                  ·
                    refine ⟨5192524509090287080693925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3461683006060191387129283 5192524509090287080693925)
                    ·
                      refine ⟨973598345454428827630111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5192524509090287080693925 973598345454428827630111)
                      ·
                        rfl

theorem cell23_1896076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1896076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896076 prefixEnd_1896076 := by exact prefixLift 1896076
  have htrace : WordTrace (prefixWord ++ tailWord_1896076) baseStart_1896076 baseEnd_1896076 := by
    simpa [prefixWord, tailWord_1896076, baseEnd_1896076] using wordTrace_append hprefix tailTrace_1896076
  have hstable : (prefixWord ++ tailWord_1896076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896076).length < 2 ^ (prefixWord ++ tailWord_1896076).sum := by decide
  have hdescent : baseEnd_1896076 < baseStart_1896076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896093 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 4, 4, 2]
def baseStart_1896093 : Nat := 118140960795 + 1896093 * 2 ^ 59
def prefixEnd_1896093 : Nat := 4983230072969 + 3 ^ 40 * 1896093 * 2
def baseEnd_1896093 : Nat := 973607074625555261117533

theorem tailTrace_1896093 : CollatzResearch.WordTrace tailWord_1896093 prefixEnd_1896093 973607074625555261117533 := by
  unfold tailWord_1896093
  simp only [CollatzResearch.WordTrace]
  refine ⟨69156193119786362748332933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46104128746524241832221955 69156193119786362748332933)
  ·
    refine ⟨12966786209959943015312425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69156193119786362748332933 12966786209959943015312425)
    ·
      refine ⟨9725089657469957261484319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12966786209959943015312425 9725089657469957261484319)
      ·
        refine ⟨14587634486204935892226479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725089657469957261484319 14587634486204935892226479)
        ·
          refine ⟨21881451729307403838339719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14587634486204935892226479 21881451729307403838339719)
          ·
            refine ⟨32822177593961105757509579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21881451729307403838339719 32822177593961105757509579)
            ·
              refine ⟨49233266390941658636264369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32822177593961105757509579 49233266390941658636264369)
              ·
                refine ⟨36924949793206243977198277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49233266390941658636264369 36924949793206243977198277)
                ·
                  refine ⟨6923428086226170745724677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36924949793206243977198277 6923428086226170745724677)
                  ·
                    refine ⟨1298142766167407014823377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6923428086226170745724677 1298142766167407014823377)
                    ·
                      refine ⟨973607074625555261117533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298142766167407014823377 973607074625555261117533)
                      ·
                        rfl

theorem cell23_1896093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_1896093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896093 prefixEnd_1896093 := by exact prefixLift 1896093
  have htrace : WordTrace (prefixWord ++ tailWord_1896093) baseStart_1896093 baseEnd_1896093 := by
    simpa [prefixWord, tailWord_1896093, baseEnd_1896093] using wordTrace_append hprefix tailTrace_1896093
  have hstable : (prefixWord ++ tailWord_1896093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896093).length < 2 ^ (prefixWord ++ tailWord_1896093).sum := by decide
  have hdescent : baseEnd_1896093 < baseStart_1896093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896167 : List Nat := [1, 1, 5, 4, 1, 2, 1, 2, 6]
def baseStart_1896167 : Nat := 118140960795 + 1896167 * 2 ^ 59
def prefixEnd_1896167 : Nat := 4983230072969 + 3 ^ 40 * 1896167 * 2
def baseEnd_1896167 : Nat := 108182785799331996843577

theorem tailTrace_1896167 : CollatzResearch.WordTrace tailWord_1896167 prefixEnd_1896167 108182785799331996843577 := by
  unfold tailWord_1896167
  simp only [CollatzResearch.WordTrace]
  refine ⟨69158892121518273386526755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46105928081012182257684503 69158892121518273386526755)
  ·
    refine ⟨103738338182277410079790133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69158892121518273386526755 103738338182277410079790133)
    ·
      refine ⟨9725469204588507194980325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103738338182277410079790133 9725469204588507194980325)
      ·
        refine ⟨1823525475860345099058811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9725469204588507194980325 1823525475860345099058811)
        ·
          refine ⟨2735288213790517648588217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823525475860345099058811 2735288213790517648588217)
          ·
            refine ⟨2051466160342888236441163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735288213790517648588217 2051466160342888236441163)
            ·
              refine ⟨3077199240514332354661745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051466160342888236441163 3077199240514332354661745)
              ·
                refine ⟨2307899430385749265996309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077199240514332354661745 2307899430385749265996309)
                ·
                  refine ⟨108182785799331996843577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2307899430385749265996309 108182785799331996843577)
                  ·
                    rfl

theorem cell23_1896167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 2, 6].length) (baseStart_1896167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896167 prefixEnd_1896167 := by exact prefixLift 1896167
  have htrace : WordTrace (prefixWord ++ tailWord_1896167) baseStart_1896167 baseEnd_1896167 := by
    simpa [prefixWord, tailWord_1896167, baseEnd_1896167] using wordTrace_append hprefix tailTrace_1896167
  have hstable : (prefixWord ++ tailWord_1896167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896167).length < 2 ^ (prefixWord ++ tailWord_1896167).sum := by decide
  have hdescent : baseEnd_1896167 < baseStart_1896167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896170 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2]
def baseStart_1896170 : Nat := 118140960795 + 1896170 * 2 ^ 59
def prefixEnd_1896170 : Nat := 4983230072969 + 3 ^ 40 * 1896170 * 2
def baseEnd_1896170 : Nat := 973646612635951459854679

theorem tailTrace_1896170 : CollatzResearch.WordTrace tailWord_1896170 prefixEnd_1896170 973646612635951459854679 := by
  unfold tailWord_1896170
  simp only [CollatzResearch.WordTrace]
  refine ⟨17289750385126851224721491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46106001027004936599257309 17289750385126851224721491)
  ·
    refine ⟨25934625577690276837082237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17289750385126851224721491 25934625577690276837082237)
    ·
      refine ⟨9725484591633853813905839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25934625577690276837082237 9725484591633853813905839)
      ·
        refine ⟨14588226887450780720858759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725484591633853813905839 14588226887450780720858759)
        ·
          refine ⟨21882340331176171081288139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588226887450780720858759 21882340331176171081288139)
          ·
            refine ⟨32823510496764256621932209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21882340331176171081288139 32823510496764256621932209)
            ·
              refine ⟨24617632872573192466449157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32823510496764256621932209 24617632872573192466449157)
              ·
                refine ⟨4615806163607473587459217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24617632872573192466449157 4615806163607473587459217)
                ·
                  refine ⟨3461854622705605190594413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4615806163607473587459217 3461854622705605190594413)
                  ·
                    refine ⟨1298195483514601946472905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3461854622705605190594413 1298195483514601946472905)
                    ·
                      refine ⟨973646612635951459854679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298195483514601946472905 973646612635951459854679)
                      ·
                        rfl

theorem cell23_1896170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_1896170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896170 prefixEnd_1896170 := by exact prefixLift 1896170
  have htrace : WordTrace (prefixWord ++ tailWord_1896170) baseStart_1896170 baseEnd_1896170 := by
    simpa [prefixWord, tailWord_1896170, baseEnd_1896170] using wordTrace_append hprefix tailTrace_1896170
  have hstable : (prefixWord ++ tailWord_1896170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896170).length < 2 ^ (prefixWord ++ tailWord_1896170).sum := by decide
  have hdescent : baseEnd_1896170 < baseStart_1896170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896177 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 1, 1, 3]
def baseStart_1896177 : Nat := 118140960795 + 1896177 * 2 ^ 59
def prefixEnd_1896177 : Nat := 4983230072969 + 3 ^ 40 * 1896177 * 2
def baseEnd_1896177 : Nat := 973650207000532932467147

theorem tailTrace_1896177 : CollatzResearch.WordTrace tailWord_1896177 prefixEnd_1896177 973650207000532932467147 := by
  unfold tailWord_1896177
  simp only [CollatzResearch.WordTrace]
  refine ⟨69159256851482045094390785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46106171234321363396260523 69159256851482045094390785)
  ·
    refine ⟨51869442638611533820793089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69159256851482045094390785 51869442638611533820793089)
    ·
      refine ⟨38902081978958650365594817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51869442638611533820793089 38902081978958650365594817)
      ·
        refine ⟨29176561484218987774196113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38902081978958650365594817 29176561484218987774196113)
        ·
          refine ⟨21882421113164240830647085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29176561484218987774196113 21882421113164240830647085)
          ·
            refine ⟨8205907917436590311492657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21882421113164240830647085 8205907917436590311492657)
            ·
              refine ⟨6154430938077442733619493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8205907917436590311492657 6154430938077442733619493)
              ·
                refine ⟨1153955800889520512553655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6154430938077442733619493 1153955800889520512553655)
                ·
                  refine ⟨1730933701334280768830483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153955800889520512553655 1730933701334280768830483)
                  ·
                    refine ⟨2596400552001421153245725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1730933701334280768830483 2596400552001421153245725)
                    ·
                      refine ⟨973650207000532932467147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596400552001421153245725 973650207000532932467147)
                      ·
                        rfl

theorem cell23_1896177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 1, 1, 3].length) (baseStart_1896177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896177 prefixEnd_1896177 := by exact prefixLift 1896177
  have htrace : WordTrace (prefixWord ++ tailWord_1896177) baseStart_1896177 baseEnd_1896177 := by
    simpa [prefixWord, tailWord_1896177, baseEnd_1896177] using wordTrace_append hprefix tailTrace_1896177
  have hstable : (prefixWord ++ tailWord_1896177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896177).length < 2 ^ (prefixWord ++ tailWord_1896177).sum := by decide
  have hdescent : baseEnd_1896177 < baseStart_1896177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896193 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1896193 : Nat := 118140960795 + 1896193 * 2 ^ 59
def prefixEnd_1896193 : Nat := 4983230072969 + 3 ^ 40 * 1896193 * 2
def baseEnd_1896193 : Nat := 324552807563668289955691

theorem tailTrace_1896193 : CollatzResearch.WordTrace tailWord_1896193 prefixEnd_1896193 324552807563668289955691 := by
  unfold tailWord_1896193
  simp only [CollatzResearch.WordTrace]
  refine ⟨69159840419424079826973233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46106560279616053217982155 69159840419424079826973233)
  ·
    refine ⟨51869880314568059870229925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69159840419424079826973233 51869880314568059870229925)
    ·
      refine ⟨9725602558981511225668111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51869880314568059870229925 9725602558981511225668111)
      ·
        refine ⟨14588403838472266838502167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725602558981511225668111 14588403838472266838502167)
        ·
          refine ⟨21882605757708400257753251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588403838472266838502167 21882605757708400257753251)
          ·
            refine ⟨32823908636562600386629877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21882605757708400257753251 32823908636562600386629877)
            ·
              refine ⟨3077241434677743786246551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32823908636562600386629877 3077241434677743786246551)
              ·
                refine ⟨4615862152016615679369827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3077241434677743786246551 4615862152016615679369827)
                ·
                  refine ⟨6923793228024923519054741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4615862152016615679369827 6923793228024923519054741)
                  ·
                    refine ⟨324552807563668289955691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6923793228024923519054741 324552807563668289955691)
                    ·
                      rfl

theorem cell23_1896193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1896193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896193 prefixEnd_1896193 := by exact prefixLift 1896193
  have htrace : WordTrace (prefixWord ++ tailWord_1896193) baseStart_1896193 baseEnd_1896193 := by
    simpa [prefixWord, tailWord_1896193, baseEnd_1896193] using wordTrace_append hprefix tailTrace_1896193
  have hstable : (prefixWord ++ tailWord_1896193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896193).length < 2 ^ (prefixWord ++ tailWord_1896193).sum := by decide
  have hdescent : baseEnd_1896193 < baseStart_1896193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896200 : List Nat := [2, 1, 3, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1896200 : Nat := 118140960795 + 1896200 * 2 ^ 59
def prefixEnd_1896200 : Nat := 4983230072969 + 3 ^ 40 * 1896200 * 2
def baseEnd_1896200 : Nat := 973662017055586342479541

theorem tailTrace_1896200 : CollatzResearch.WordTrace tailWord_1896200 prefixEnd_1896200 973662017055586342479541 := by
  unfold tailWord_1896200
  simp only [CollatzResearch.WordTrace]
  refine ⟨34580047865199360011239027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46106730486932480014985369 34580047865199360011239027)
  ·
    refine ⟨51870071797799040016858541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34580047865199360011239027 51870071797799040016858541)
    ·
      refine ⟨19451276924174640006321953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51870071797799040016858541 19451276924174640006321953)
      ·
        refine ⟨14588457693130980004741465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19451276924174640006321953 14588457693130980004741465)
        ·
          refine ⟨10941343269848235003556099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14588457693130980004741465 10941343269848235003556099)
          ·
            refine ⟨16412014904772352505334149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10941343269848235003556099 16412014904772352505334149)
            ·
              refine ⟨3077252794644816094750153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16412014904772352505334149 3077252794644816094750153)
              ·
                refine ⟨2307939595983612071062615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077252794644816094750153 2307939595983612071062615)
                ·
                  refine ⟨3461909393975418106593923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307939595983612071062615 3461909393975418106593923)
                  ·
                    refine ⟨5192864090963127159890885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3461909393975418106593923 5192864090963127159890885)
                    ·
                      refine ⟨973662017055586342479541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5192864090963127159890885 973662017055586342479541)
                      ·
                        rfl

theorem cell23_1896200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1896200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896200 prefixEnd_1896200 := by exact prefixLift 1896200
  have htrace : WordTrace (prefixWord ++ tailWord_1896200) baseStart_1896200 baseEnd_1896200 := by
    simpa [prefixWord, tailWord_1896200, baseEnd_1896200] using wordTrace_append hprefix tailTrace_1896200
  have hstable : (prefixWord ++ tailWord_1896200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896200).length < 2 ^ (prefixWord ++ tailWord_1896200).sum := by decide
  have hdescent : baseEnd_1896200 < baseStart_1896200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896203 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 3]
def baseStart_1896203 : Nat := 118140960795 + 1896203 * 2 ^ 59
def prefixEnd_1896203 : Nat := 4983230072969 + 3 ^ 40 * 1896203 * 2
def baseEnd_1896203 : Nat := 973663557497549830742027

theorem tailTrace_1896203 : CollatzResearch.WordTrace tailWord_1896203 prefixEnd_1896203 973663557497549830742027 := by
  unfold tailWord_1896203
  simp only [CollatzResearch.WordTrace]
  refine ⟨69160205149387851534837263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46106803432925234356558175 69160205149387851534837263)
  ·
    refine ⟨103740307724081777302255895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69160205149387851534837263 103740307724081777302255895)
    ·
      refine ⟨155610461586122665953383843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103740307724081777302255895 155610461586122665953383843)
      ·
        refine ⟨233415692379183998930075765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155610461586122665953383843 233415692379183998930075765)
        ·
          refine ⟨21882721160548499899694603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 233415692379183998930075765 21882721160548499899694603)
          ·
            refine ⟨32824081740822749849541905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21882721160548499899694603 32824081740822749849541905)
            ·
              refine ⟨24618061305617062387156429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32824081740822749849541905 24618061305617062387156429)
              ·
                refine ⟨9231772989606398395183661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24618061305617062387156429 9231772989606398395183661)
                ·
                  refine ⟨3461914871102399398193873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9231772989606398395183661 3461914871102399398193873)
                  ·
                    refine ⟨2596436153326799548645405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461914871102399398193873 2596436153326799548645405)
                    ·
                      refine ⟨973663557497549830742027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596436153326799548645405 973663557497549830742027)
                      ·
                        rfl

theorem cell23_1896203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 2, 3].length) (baseStart_1896203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896203 prefixEnd_1896203 := by exact prefixLift 1896203
  have htrace : WordTrace (prefixWord ++ tailWord_1896203) baseStart_1896203 baseEnd_1896203 := by
    simpa [prefixWord, tailWord_1896203, baseEnd_1896203] using wordTrace_append hprefix tailTrace_1896203
  have hstable : (prefixWord ++ tailWord_1896203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896203).length < 2 ^ (prefixWord ++ tailWord_1896203).sum := by decide
  have hdescent : baseEnd_1896203 < baseStart_1896203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896205 : List Nat := [1, 7, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1896205 : Nat := 118140960795 + 1896205 * 2 ^ 59
def prefixEnd_1896205 : Nat := 4983230072969 + 3 ^ 40 * 1896205 * 2
def baseEnd_1896205 : Nat := 324554861486286274305673

theorem tailTrace_1896205 : CollatzResearch.WordTrace tailWord_1896205 prefixEnd_1896205 324554861486286274305673 := by
  unfold tailWord_1896205
  simp only [CollatzResearch.WordTrace]
  refine ⟨69160278095380605876410069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46106852063587070584273379 69160278095380605876410069)
  ·
    refine ⟨1620944017860482950228361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 69160278095380605876410069 1620944017860482950228361)
    ·
      refine ⟨1215708013395362212671271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1620944017860482950228361 1215708013395362212671271)
      ·
        refine ⟨1823562020093043319006907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1215708013395362212671271 1823562020093043319006907)
        ·
          refine ⟨2735343030139564978510361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1823562020093043319006907 2735343030139564978510361)
          ·
            refine ⟨2051507272604673733882771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735343030139564978510361 2051507272604673733882771)
            ·
              refine ⟨3077260908907010600824157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051507272604673733882771 3077260908907010600824157)
              ·
                refine ⟨1153972840840128975309059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3077260908907010600824157 1153972840840128975309059)
                ·
                  refine ⟨1730959261260193462963589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1153972840840128975309059 1730959261260193462963589)
                  ·
                    refine ⟨324554861486286274305673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730959261260193462963589 324554861486286274305673)
                    ·
                      rfl

theorem cell23_1896205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1896205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896205 prefixEnd_1896205 := by exact prefixLift 1896205
  have htrace : WordTrace (prefixWord ++ tailWord_1896205) baseStart_1896205 baseEnd_1896205 := by
    simpa [prefixWord, tailWord_1896205, baseEnd_1896205] using wordTrace_append hprefix tailTrace_1896205
  have hstable : (prefixWord ++ tailWord_1896205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896205).length < 2 ^ (prefixWord ++ tailWord_1896205).sum := by decide
  have hdescent : baseEnd_1896205 < baseStart_1896205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896220 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 1, 2, 3]
def baseStart_1896220 : Nat := 118140960795 + 1896220 * 2 ^ 59
def prefixEnd_1896220 : Nat := 4983230072969 + 3 ^ 40 * 1896220 * 2
def baseEnd_1896220 : Nat := 973672286668676264229449

theorem tailTrace_1896220 : CollatzResearch.WordTrace tailWord_1896220 prefixEnd_1896220 973672286668676264229449 := by
  unfold tailWord_1896220
  simp only [CollatzResearch.WordTrace]
  refine ⟨34580412595163131719103057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46107216793550842292137409 34580412595163131719103057)
  ·
    refine ⟨25935309446372348789327293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34580412595163131719103057 25935309446372348789327293)
    ·
      refine ⟨9725741042389630795997735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25935309446372348789327293 9725741042389630795997735)
      ·
        refine ⟨14588611563584446193996603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9725741042389630795997735 14588611563584446193996603)
        ·
          refine ⟨21882917345376669290994905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14588611563584446193996603 21882917345376669290994905)
          ·
            refine ⟨16412188009032501968246179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21882917345376669290994905 16412188009032501968246179)
            ·
              refine ⟨24618282013548752952369269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16412188009032501968246179 24618282013548752952369269)
              ·
                refine ⟨2307963938770195589284619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24618282013548752952369269 2307963938770195589284619)
                ·
                  refine ⟨3461945908155293383926929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2307963938770195589284619 3461945908155293383926929)
                  ·
                    refine ⟨2596459431116470037945197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3461945908155293383926929 2596459431116470037945197)
                    ·
                      refine ⟨973672286668676264229449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596459431116470037945197 973672286668676264229449)
                      ·
                        rfl

theorem cell23_1896220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_1896220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896220 prefixEnd_1896220 := by exact prefixLift 1896220
  have htrace : WordTrace (prefixWord ++ tailWord_1896220) baseStart_1896220 baseEnd_1896220 := by
    simpa [prefixWord, tailWord_1896220, baseEnd_1896220] using wordTrace_append hprefix tailTrace_1896220
  have hstable : (prefixWord ++ tailWord_1896220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896220).length < 2 ^ (prefixWord ++ tailWord_1896220).sum := by decide
  have hdescent : baseEnd_1896220 < baseStart_1896220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896244 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1896244 : Nat := 118140960795 + 1896244 * 2 ^ 59
def prefixEnd_1896244 : Nat := 4983230072969 + 3 ^ 40 * 1896244 * 2
def baseEnd_1896244 : Nat := 324561536734794723443113

theorem tailTrace_1896244 : CollatzResearch.WordTrace tailWord_1896244 prefixEnd_1896244 324561536734794723443113 := by
  unfold tailWord_1896244
  simp only [CollatzResearch.WordTrace]
  refine ⟨34580850271119657768539893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46107800361492877024719857 34580850271119657768539893)
  ·
    refine ⟨3241954712917467915800615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34580850271119657768539893 3241954712917467915800615)
    ·
      refine ⟨4862932069376201873700923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3241954712917467915800615 4862932069376201873700923)
      ·
        refine ⟨7294398104064302810551385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4862932069376201873700923 7294398104064302810551385)
        ·
          refine ⟨5470798578048227107913539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7294398104064302810551385 5470798578048227107913539)
          ·
            refine ⟨8206197867072340661870309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470798578048227107913539 8206197867072340661870309)
            ·
              refine ⟨1538662100076063874100683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8206197867072340661870309 1538662100076063874100683)
              ·
                refine ⟨2307993150114095811151025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538662100076063874100683 2307993150114095811151025)
                ·
                  refine ⟨1730994862585571858363269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2307993150114095811151025 1730994862585571858363269)
                  ·
                    refine ⟨324561536734794723443113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1730994862585571858363269 324561536734794723443113)
                    ·
                      rfl

theorem cell23_1896244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1896244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896244 prefixEnd_1896244 := by exact prefixLift 1896244
  have htrace : WordTrace (prefixWord ++ tailWord_1896244) baseStart_1896244 baseEnd_1896244 := by
    simpa [prefixWord, tailWord_1896244, baseEnd_1896244] using wordTrace_append hprefix tailTrace_1896244
  have hstable : (prefixWord ++ tailWord_1896244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896244).length < 2 ^ (prefixWord ++ tailWord_1896244).sum := by decide
  have hdescent : baseEnd_1896244 < baseStart_1896244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896254 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_1896254 : Nat := 118140960795 + 1896254 * 2 ^ 59
def prefixEnd_1896254 : Nat := 4983230072969 + 3 ^ 40 * 1896254 * 2
def baseEnd_1896254 : Nat := 973689745010929131204293

theorem tailTrace_1896254 : CollatzResearch.WordTrace tailWord_1896254 prefixEnd_1896254 973689745010929131204293 := by
  unfold tailWord_1896254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8645258159025385905617977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46108043514802058163295877 8645258159025385905617977)
  ·
    refine ⟨6483943619269039429213483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8645258159025385905617977 6483943619269039429213483)
    ·
      refine ⟨9725915428903559143820225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6483943619269039429213483 9725915428903559143820225)
      ·
        refine ⟨7294436571677669357865169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9725915428903559143820225 7294436571677669357865169)
        ·
          refine ⟨5470827428758252018398877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7294436571677669357865169 5470827428758252018398877)
          ·
            refine ⟨2051560285784344506899579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5470827428758252018398877 2051560285784344506899579)
            ·
              refine ⟨3077340428676516760349369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2051560285784344506899579 3077340428676516760349369)
              ·
                refine ⟨2308005321507387570262027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3077340428676516760349369 2308005321507387570262027)
                ·
                  refine ⟨3462007982261081355393041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308005321507387570262027 3462007982261081355393041)
                  ·
                    refine ⟨2596505986695811016544781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462007982261081355393041 2596505986695811016544781)
                    ·
                      refine ⟨973689745010929131204293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596505986695811016544781 973689745010929131204293)
                      ·
                        rfl

theorem cell23_1896254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_1896254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896254 prefixEnd_1896254 := by exact prefixLift 1896254
  have htrace : WordTrace (prefixWord ++ tailWord_1896254) baseStart_1896254 baseEnd_1896254 := by
    simpa [prefixWord, tailWord_1896254, baseEnd_1896254] using wordTrace_append hprefix tailTrace_1896254
  have hstable : (prefixWord ++ tailWord_1896254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896254).length < 2 ^ (prefixWord ++ tailWord_1896254).sum := by decide
  have hdescent : baseEnd_1896254 < baseStart_1896254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896256 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1896256 : Nat := 118140960795 + 1896256 * 2 ^ 59
def prefixEnd_1896256 : Nat := 4983230072969 + 3 ^ 40 * 1896256 * 2
def baseEnd_1896256 : Nat := 973690771972238123379283

theorem tailTrace_1896256 : CollatzResearch.WordTrace tailWord_1896256 prefixEnd_1896256 973690771972238123379283 := by
  unfold tailWord_1896256
  simp only [CollatzResearch.WordTrace]
  refine ⟨34581069109097920793258311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46108092145463894391011081 34581069109097920793258311)
  ·
    refine ⟨51871603663646881189887467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34581069109097920793258311 51871603663646881189887467)
    ·
      refine ⟨77807405495470321784831201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51871603663646881189887467 77807405495470321784831201)
      ·
        refine ⟨58355554121602741338623401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77807405495470321784831201 58355554121602741338623401)
        ·
          refine ⟨43766665591202056003967551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58355554121602741338623401 43766665591202056003967551)
          ·
            refine ⟨65649998386803084005951327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43766665591202056003967551 65649998386803084005951327)
            ·
              refine ⟨98474997580204626008926991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65649998386803084005951327 98474997580204626008926991)
              ·
                refine ⟨147712496370306939013390487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 98474997580204626008926991 147712496370306939013390487)
                ·
                  refine ⟨221568744555460408520085731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147712496370306939013390487 221568744555460408520085731)
                  ·
                    refine ⟨332353116833190612780128597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 221568744555460408520085731 332353116833190612780128597)
                    ·
                      refine ⟨973690771972238123379283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 332353116833190612780128597 973690771972238123379283)
                      ·
                        rfl

theorem cell23_1896256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1896256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896256 prefixEnd_1896256 := by exact prefixLift 1896256
  have htrace : WordTrace (prefixWord ++ tailWord_1896256) baseStart_1896256 baseEnd_1896256 := by
    simpa [prefixWord, tailWord_1896256, baseEnd_1896256] using wordTrace_append hprefix tailTrace_1896256
  have hstable : (prefixWord ++ tailWord_1896256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896256).length < 2 ^ (prefixWord ++ tailWord_1896256).sum := by decide
  have hdescent : baseEnd_1896256 < baseStart_1896256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896290 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_1896290 : Nat := 118140960795 + 1896290 * 2 ^ 59
def prefixEnd_1896290 : Nat := 4983230072969 + 3 ^ 40 * 1896290 * 2
def baseEnd_1896290 : Nat := 973708230314490990354127

theorem tailTrace_1896290 : CollatzResearch.WordTrace tailWord_1896290 prefixEnd_1896290 973708230314490990354127 := by
  unfold tailWord_1896290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17290844575018166348313581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46108918866715110262169549 17290844575018166348313581)
  ·
    refine ⟨6484066715631812380617593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17290844575018166348313581 6484066715631812380617593)
    ·
      refine ⟨4863050036723859285463195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6484066715631812380617593 4863050036723859285463195)
      ·
        refine ⟨7294575055085788928194793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863050036723859285463195 7294575055085788928194793)
        ·
          refine ⟨5470931291314341696146095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7294575055085788928194793 5470931291314341696146095)
          ·
            refine ⟨8206396936971512544219143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470931291314341696146095 8206396936971512544219143)
            ·
              refine ⟨12309595405457268816328715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8206396936971512544219143 12309595405457268816328715)
              ·
                refine ⟨18464393108185903224493073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12309595405457268816328715 18464393108185903224493073)
                ·
                  refine ⟨13848294831139427418369805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18464393108185903224493073 13848294831139427418369805)
                  ·
                    refine ⟨5193110561677285281888677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13848294831139427418369805 5193110561677285281888677)
                    ·
                      refine ⟨973708230314490990354127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5193110561677285281888677 973708230314490990354127)
                      ·
                        rfl

theorem cell23_1896290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_1896290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896290 prefixEnd_1896290 := by exact prefixLift 1896290
  have htrace : WordTrace (prefixWord ++ tailWord_1896290) baseStart_1896290 baseEnd_1896290 := by
    simpa [prefixWord, tailWord_1896290, baseEnd_1896290] using wordTrace_append hprefix tailTrace_1896290
  have hstable : (prefixWord ++ tailWord_1896290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896290).length < 2 ^ (prefixWord ++ tailWord_1896290).sum := by decide
  have hdescent : baseEnd_1896290 < baseStart_1896290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896313 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 7]
def baseStart_1896313 : Nat := 118140960795 + 1896313 * 2 ^ 59
def prefixEnd_1896313 : Nat := 4983230072969 + 3 ^ 40 * 1896313 * 2
def baseEnd_1896313 : Nat := 108191115596616044485169

theorem tailTrace_1896313 : CollatzResearch.WordTrace tailWord_1896313 prefixEnd_1896313 108191115596616044485169 := by
  unfold tailWord_1896313
  simp only [CollatzResearch.WordTrace]
  refine ⟨69164217178989340321341593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46109478119326226880894395 69164217178989340321341593)
  ·
    refine ⟨51873162884242005241006195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69164217178989340321341593 51873162884242005241006195)
    ·
      refine ⟨77809744326363007861509293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51873162884242005241006195 77809744326363007861509293)
      ·
        refine ⟨29178654122386127948065985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77809744326363007861509293 29178654122386127948065985)
        ·
          refine ⟨21883990591789595961049489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29178654122386127948065985 21883990591789595961049489)
          ·
            refine ⟨16412992943842196970787117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21883990591789595961049489 16412992943842196970787117)
            ·
              refine ⟨6154872353940823864045169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16412992943842196970787117 6154872353940823864045169)
              ·
                refine ⟨4616154265455617898033877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6154872353940823864045169 4616154265455617898033877)
                ·
                  refine ⟨108191115596616044485169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4616154265455617898033877 108191115596616044485169)
                  ·
                    rfl

theorem cell23_1896313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_1896313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896313 prefixEnd_1896313 := by exact prefixLift 1896313
  have htrace : WordTrace (prefixWord ++ tailWord_1896313) baseStart_1896313 baseEnd_1896313 := by
    simpa [prefixWord, tailWord_1896313, baseEnd_1896313] using wordTrace_append hprefix tailTrace_1896313
  have hstable : (prefixWord ++ tailWord_1896313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896313).length < 2 ^ (prefixWord ++ tailWord_1896313).sum := by decide
  have hdescent : baseEnd_1896313 < baseStart_1896313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896328 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 1, 3, 2]
def baseStart_1896328 : Nat := 118140960795 + 1896328 * 2 ^ 59
def prefixEnd_1896328 : Nat := 4983230072969 + 3 ^ 40 * 1896328 * 2
def baseEnd_1896328 : Nat := 973727742579361841678953

theorem tailTrace_1896328 : CollatzResearch.WordTrace tailWord_1896328 prefixEnd_1896328 973727742579361841678953 := by
  unfold tailWord_1896328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34582382136967498941568819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46109842849289998588758425 34582382136967498941568819)
  ·
    refine ⟨51873573205451248412353229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34582382136967498941568819 51873573205451248412353229)
    ·
      refine ⟨19452589952044218154632461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51873573205451248412353229 19452589952044218154632461)
      ·
        refine ⟨7294721232016581807987173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19452589952044218154632461 7294721232016581807987173)
        ·
          refine ⟨1367760231003109088997595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7294721232016581807987173 1367760231003109088997595)
          ·
            refine ⟨2051640346504663633496393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1367760231003109088997595 2051640346504663633496393)
            ·
              refine ⟨1538730259878497725122295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051640346504663633496393 1538730259878497725122295)
              ·
                refine ⟨2308095389817746587683443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538730259878497725122295 2308095389817746587683443)
                ·
                  refine ⟨3462143084726619881525165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308095389817746587683443 3462143084726619881525165)
                  ·
                    refine ⟨1298303656772482455571937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3462143084726619881525165 1298303656772482455571937)
                    ·
                      refine ⟨973727742579361841678953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298303656772482455571937 973727742579361841678953)
                      ·
                        rfl

theorem cell23_1896328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_1896328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896328 prefixEnd_1896328 := by exact prefixLift 1896328
  have htrace : WordTrace (prefixWord ++ tailWord_1896328) baseStart_1896328 baseEnd_1896328 := by
    simpa [prefixWord, tailWord_1896328, baseEnd_1896328] using wordTrace_append hprefix tailTrace_1896328
  have hstable : (prefixWord ++ tailWord_1896328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896328).length < 2 ^ (prefixWord ++ tailWord_1896328).sum := by decide
  have hdescent : baseEnd_1896328 < baseStart_1896328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896393 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_1896393 : Nat := 118140960795 + 1896393 * 2 ^ 59
def prefixEnd_1896393 : Nat := 4983230072969 + 3 ^ 40 * 1896393 * 2
def baseEnd_1896393 : Nat := 973761118821904087366153

theorem tailTrace_1896393 : CollatzResearch.WordTrace tailWord_1896393 prefixEnd_1896393 973761118821904087366153 := by
  unfold tailWord_1896393
  simp only [CollatzResearch.WordTrace]
  refine ⟨69167135018699513984253833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46111423345799675989502555 69167135018699513984253833)
  ·
    refine ⟨51875351264024635488190375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69167135018699513984253833 51875351264024635488190375)
    ·
      refine ⟨77813026896036953232285563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51875351264024635488190375 77813026896036953232285563)
      ·
        refine ⟨116719540344055429848428345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77813026896036953232285563 116719540344055429848428345)
        ·
          refine ⟨87539655258041572386321259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116719540344055429848428345 87539655258041572386321259)
          ·
            refine ⟨131309482887062358579481889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87539655258041572386321259 131309482887062358579481889)
            ·
              refine ⟨98482112165296768934611417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131309482887062358579481889 98482112165296768934611417)
              ·
                refine ⟨73861584123972576700958563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98482112165296768934611417 73861584123972576700958563)
                ·
                  refine ⟨110792376185958865051437845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73861584123972576700958563 110792376185958865051437845)
                  ·
                    refine ⟨5193392633716821799286149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 110792376185958865051437845 5193392633716821799286149)
                    ·
                      refine ⟨973761118821904087366153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5193392633716821799286149 973761118821904087366153)
                      ·
                        rfl

theorem cell23_1896393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_1896393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896393 prefixEnd_1896393 := by exact prefixLift 1896393
  have htrace : WordTrace (prefixWord ++ tailWord_1896393) baseStart_1896393 baseEnd_1896393 := by
    simpa [prefixWord, tailWord_1896393, baseEnd_1896393] using wordTrace_append hprefix tailTrace_1896393
  have hstable : (prefixWord ++ tailWord_1896393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896393).length < 2 ^ (prefixWord ++ tailWord_1896393).sum := by decide
  have hdescent : baseEnd_1896393 < baseStart_1896393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896400 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3]
def baseStart_1896400 : Nat := 118140960795 + 1896400 * 2 ^ 59
def prefixEnd_1896400 : Nat := 4983230072969 + 3 ^ 40 * 1896400 * 2
def baseEnd_1896400 : Nat := 973764713186485559978621

theorem tailTrace_1896400 : CollatzResearch.WordTrace tailWord_1896400 prefixEnd_1896400 973764713186485559978621 := by
  unfold tailWord_1896400
  simp only [CollatzResearch.WordTrace]
  refine ⟨34583695164837077089879327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46111593553116102786505769 34583695164837077089879327)
  ·
    refine ⟨51875542747255615634818991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34583695164837077089879327 51875542747255615634818991)
    ·
      refine ⟨77813314120883423452228487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51875542747255615634818991 77813314120883423452228487)
      ·
        refine ⟨116719971181325135178342731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77813314120883423452228487 116719971181325135178342731)
        ·
          refine ⟨175079956771987702767514097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116719971181325135178342731 175079956771987702767514097)
          ·
            refine ⟨131309967578990777075635573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175079956771987702767514097 131309967578990777075635573)
            ·
              refine ⟨12310309460530385350840835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131309967578990777075635573 12310309460530385350840835)
              ·
                refine ⟨18465464190795578026261253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12310309460530385350840835 18465464190795578026261253)
                ·
                  refine ⟨3462274535774170879923985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18465464190795578026261253 3462274535774170879923985)
                  ·
                    refine ⟨2596705901830628159942989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462274535774170879923985 2596705901830628159942989)
                    ·
                      refine ⟨973764713186485559978621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596705901830628159942989 973764713186485559978621)
                      ·
                        rfl

theorem cell23_1896400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_1896400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896400 prefixEnd_1896400 := by exact prefixLift 1896400
  have htrace : WordTrace (prefixWord ++ tailWord_1896400) baseStart_1896400 baseEnd_1896400 := by
    simpa [prefixWord, tailWord_1896400, baseEnd_1896400] using wordTrace_append hprefix tailTrace_1896400
  have hstable : (prefixWord ++ tailWord_1896400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896400).length < 2 ^ (prefixWord ++ tailWord_1896400).sum := by decide
  have hdescent : baseEnd_1896400 < baseStart_1896400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896420 : List Nat := [2, 3, 1, 1, 1, 1, 5, 3, 6]
def baseStart_1896420 : Nat := 118140960795 + 1896420 * 2 ^ 59
def prefixEnd_1896420 : Nat := 4983230072969 + 3 ^ 40 * 1896420 * 2
def baseEnd_1896420 : Nat := 108197220311063942414281

theorem tailTrace_1896420 : CollatzResearch.WordTrace tailWord_1896420 prefixEnd_1896420 108197220311063942414281 := by
  unfold tailWord_1896420
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584059894800848797743357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46112079859734465063657809 34584059894800848797743357)
  ·
    refine ⟨12969022460550318299153759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34584059894800848797743357 12969022460550318299153759)
    ·
      refine ⟨19453533690825477448730639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12969022460550318299153759 19453533690825477448730639)
      ·
        refine ⟨29180300536238216173095959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19453533690825477448730639 29180300536238216173095959)
        ·
          refine ⟨43770450804357324259643939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29180300536238216173095959 43770450804357324259643939)
          ·
            refine ⟨65655676206535986389465909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43770450804357324259643939 65655676206535986389465909)
            ·
              refine ⟨6155219644362748724012429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65655676206535986389465909 6155219644362748724012429)
              ·
                refine ⟨2308207366636030771504661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6155219644362748724012429 2308207366636030771504661)
                ·
                  refine ⟨108197220311063942414281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2308207366636030771504661 108197220311063942414281)
                  ·
                    rfl

theorem cell23_1896420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_1896420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896420 prefixEnd_1896420 := by exact prefixLift 1896420
  have htrace : WordTrace (prefixWord ++ tailWord_1896420) baseStart_1896420 baseEnd_1896420 := by
    simpa [prefixWord, tailWord_1896420, baseEnd_1896420] using wordTrace_append hprefix tailTrace_1896420
  have hstable : (prefixWord ++ tailWord_1896420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896420).length < 2 ^ (prefixWord ++ tailWord_1896420).sum := by decide
  have hdescent : baseEnd_1896420 < baseStart_1896420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896458 : List Nat := [3, 1, 2, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1896458 : Nat := 118140960795 + 1896458 * 2 ^ 59
def prefixEnd_1896458 : Nat := 4983230072969 + 3 ^ 40 * 1896458 * 2
def baseEnd_1896458 : Nat := 324598165021482111017785

theorem tailTrace_1896458 : CollatzResearch.WordTrace tailWord_1896458 prefixEnd_1896458 324598165021482111017785 := by
  unfold tailWord_1896458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17292376440866007521342507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46113003842309353390246685 17292376440866007521342507)
  ·
    refine ⟨25938564661299011282013761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17292376440866007521342507 25938564661299011282013761)
    ·
      refine ⟨19453923495974258461510321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25938564661299011282013761 19453923495974258461510321)
      ·
        refine ⟨14590442621980693846132741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19453923495974258461510321 14590442621980693846132741)
        ·
          refine ⟨2735707991621380096149889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14590442621980693846132741 2735707991621380096149889)
          ·
            refine ⟨2051780993716035072112417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2735707991621380096149889 2051780993716035072112417)
            ·
              refine ⟨1538835745287026304084313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2051780993716035072112417 1538835745287026304084313)
              ·
                refine ⟨1154126808965269728063235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1538835745287026304084313 1154126808965269728063235)
                ·
                  refine ⟨1731190213447904592094853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154126808965269728063235 1731190213447904592094853)
                  ·
                    refine ⟨324598165021482111017785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1731190213447904592094853 324598165021482111017785)
                    ·
                      rfl

theorem cell23_1896458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1896458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896458 prefixEnd_1896458 := by exact prefixLift 1896458
  have htrace : WordTrace (prefixWord ++ tailWord_1896458) baseStart_1896458 baseEnd_1896458 := by
    simpa [prefixWord, tailWord_1896458, baseEnd_1896458] using wordTrace_append hprefix tailTrace_1896458
  have hstable : (prefixWord ++ tailWord_1896458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896458).length < 2 ^ (prefixWord ++ tailWord_1896458).sum := by decide
  have hdescent : baseEnd_1896458 < baseStart_1896458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896463 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 1, 12]
def baseStart_1896463 : Nat := 118140960795 + 1896463 * 2 ^ 59
def prefixEnd_1896463 : Nat := 4983230072969 + 3 ^ 40 * 1896463 * 2
def baseEnd_1896463 : Nat := 324599020822572937830277

theorem tailTrace_1896463 : CollatzResearch.WordTrace tailWord_1896463 prefixEnd_1896463 324599020822572937830277 := by
  unfold tailWord_1896463
  simp only [CollatzResearch.WordTrace]
  refine ⟨69169688128445915939302043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46113125418963943959534695 69169688128445915939302043)
  ·
    refine ⟨103754532192668873908953065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69169688128445915939302043 103754532192668873908953065)
    ·
      refine ⟨77815899144501655431714799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103754532192668873908953065 77815899144501655431714799)
      ·
        refine ⟨116723848716752483147572199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77815899144501655431714799 116723848716752483147572199)
        ·
          refine ⟨175085773075128724721358299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116723848716752483147572199 175085773075128724721358299)
          ·
            refine ⟨262628659612693087082037449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175085773075128724721358299 262628659612693087082037449)
            ·
              refine ⟨196971494709519815311528087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262628659612693087082037449 196971494709519815311528087)
              ·
                refine ⟨295457242064279722967292131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196971494709519815311528087 295457242064279722967292131)
                ·
                  refine ⟨443185863096419584450938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 295457242064279722967292131 443185863096419584450938197)
                  ·
                    refine ⟨324599020822572937830277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 443185863096419584450938197 324599020822572937830277)
                    ·
                      rfl

theorem cell23_1896463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_1896463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896463 prefixEnd_1896463 := by exact prefixLift 1896463
  have htrace : WordTrace (prefixWord ++ tailWord_1896463) baseStart_1896463 baseEnd_1896463 := by
    simpa [prefixWord, tailWord_1896463, baseEnd_1896463] using wordTrace_append hprefix tailTrace_1896463
  have hstable : (prefixWord ++ tailWord_1896463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896463).length < 2 ^ (prefixWord ++ tailWord_1896463).sum := by decide
  have hdescent : baseEnd_1896463 < baseStart_1896463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896464 : List Nat := [2, 1, 1, 1, 1, 1, 1, 10, 1, 1, 3]
def baseStart_1896464 : Nat := 118140960795 + 1896464 * 2 ^ 59
def prefixEnd_1896464 : Nat := 4983230072969 + 3 ^ 40 * 1896464 * 2
def baseEnd_1896464 : Nat := 973797575948373309578327

theorem tailTrace_1896464 : CollatzResearch.WordTrace tailWord_1896464 prefixEnd_1896464 973797575948373309578327 := by
  unfold tailWord_1896464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34584862300721146555044223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46113149734294862073392297 34584862300721146555044223)
  ·
    refine ⟨51877293451081719832566335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34584862300721146555044223 51877293451081719832566335)
    ·
      refine ⟨77815940176622579748849503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51877293451081719832566335 77815940176622579748849503)
      ·
        refine ⟨116723910264933869623274255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77815940176622579748849503 116723910264933869623274255)
        ·
          refine ⟨175085865397400804434911383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116723910264933869623274255 175085865397400804434911383)
          ·
            refine ⟨262628798096101206652367075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175085865397400804434911383 262628798096101206652367075)
            ·
              refine ⟨393943197144151809978550613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262628798096101206652367075 393943197144151809978550613)
              ·
                refine ⟨1154130460383257255796535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 393943197144151809978550613 1154130460383257255796535)
                ·
                  refine ⟨1731195690574885883694803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154130460383257255796535 1731195690574885883694803)
                  ·
                    refine ⟨2596793535862328825542205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1731195690574885883694803 2596793535862328825542205)
                    ·
                      refine ⟨973797575948373309578327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596793535862328825542205 973797575948373309578327)
                      ·
                        rfl

theorem cell23_1896464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10, 1, 1, 3].length) (baseStart_1896464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896464 prefixEnd_1896464 := by exact prefixLift 1896464
  have htrace : WordTrace (prefixWord ++ tailWord_1896464) baseStart_1896464 baseEnd_1896464 := by
    simpa [prefixWord, tailWord_1896464, baseEnd_1896464] using wordTrace_append hprefix tailTrace_1896464
  have hstable : (prefixWord ++ tailWord_1896464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896464).length < 2 ^ (prefixWord ++ tailWord_1896464).sum := by decide
  have hdescent : baseEnd_1896464 < baseStart_1896464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896504 : List Nat := [2, 1, 2, 1, 6, 1, 1, 3, 1, 1, 4]
def baseStart_1896504 : Nat := 118140960795 + 1896504 * 2 ^ 59
def prefixEnd_1896504 : Nat := 4983230072969 + 3 ^ 40 * 1896504 * 2
def baseEnd_1896504 : Nat := 973818115174553153078143

theorem tailTrace_1896504 : CollatzResearch.WordTrace tailWord_1896504 prefixEnd_1896504 973818115174553153078143 := by
  unfold tailWord_1896504
  simp only [CollatzResearch.WordTrace]
  refine ⟨34585591760648689970772283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46114122347531586627696377 34585591760648689970772283)
  ·
    refine ⟨51878387640973034956158425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34585591760648689970772283 51878387640973034956158425)
    ·
      refine ⟨38908790730729776217118819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51878387640973034956158425 38908790730729776217118819)
      ·
        refine ⟨58363186096094664325678229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38908790730729776217118819 58363186096094664325678229)
        ·
          refine ⟨2735774348254437390266167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58363186096094664325678229 2735774348254437390266167)
          ·
            refine ⟨4103661522381656085399251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735774348254437390266167 4103661522381656085399251)
            ·
              refine ⟨6155492283572484128098877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103661522381656085399251 6155492283572484128098877)
              ·
                refine ⟨2308309606339681548037079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6155492283572484128098877 2308309606339681548037079)
                ·
                  refine ⟨3462464409509522322055619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308309606339681548037079 3462464409509522322055619)
                  ·
                    refine ⟨5193696614264283483083429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3462464409509522322055619 5193696614264283483083429)
                    ·
                      refine ⟨973818115174553153078143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5193696614264283483083429 973818115174553153078143)
                      ·
                        rfl

theorem cell23_1896504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 1, 4].length) (baseStart_1896504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896504 prefixEnd_1896504 := by exact prefixLift 1896504
  have htrace : WordTrace (prefixWord ++ tailWord_1896504) baseStart_1896504 baseEnd_1896504 := by
    simpa [prefixWord, tailWord_1896504, baseEnd_1896504] using wordTrace_append hprefix tailTrace_1896504
  have hstable : (prefixWord ++ tailWord_1896504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896504).length < 2 ^ (prefixWord ++ tailWord_1896504).sum := by decide
  have hdescent : baseEnd_1896504 < baseStart_1896504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896507 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 3]
def baseStart_1896507 : Nat := 118140960795 + 1896507 * 2 ^ 59
def prefixEnd_1896507 : Nat := 4983230072969 + 3 ^ 40 * 1896507 * 2
def baseEnd_1896507 : Nat := 973819655616516641340629

theorem tailTrace_1896507 : CollatzResearch.WordTrace tailWord_1896507 prefixEnd_1896507 973819655616516641340629 := by
  unfold tailWord_1896507
  simp only [CollatzResearch.WordTrace]
  refine ⟨69171292940286511453903775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46114195293524340969269183 69171292940286511453903775)
  ·
    refine ⟨103756939410429767180855663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69171292940286511453903775 103756939410429767180855663)
    ·
      refine ⟨155635409115644650771283495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103756939410429767180855663 155635409115644650771283495)
      ·
        refine ⟨233453113673466976156925243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155635409115644650771283495 233453113673466976156925243)
        ·
          refine ⟨350179670510200464235387865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233453113673466976156925243 350179670510200464235387865)
          ·
            refine ⟨262634752882650348176540899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350179670510200464235387865 262634752882650348176540899)
            ·
              refine ⟨393952129323975522264811349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 262634752882650348176540899 393952129323975522264811349)
              ·
                refine ⟨2308313257757669075770379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 393952129323975522264811349 2308313257757669075770379)
                ·
                  refine ⟨3462469886636503613655569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308313257757669075770379 3462469886636503613655569)
                  ·
                    refine ⟨2596852414977377710241677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462469886636503613655569 2596852414977377710241677)
                    ·
                      refine ⟨973819655616516641340629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596852414977377710241677 973819655616516641340629)
                      ·
                        rfl

theorem cell23_1896507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 3].length) (baseStart_1896507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896507 prefixEnd_1896507 := by exact prefixLift 1896507
  have htrace : WordTrace (prefixWord ++ tailWord_1896507) baseStart_1896507 baseEnd_1896507 := by
    simpa [prefixWord, tailWord_1896507, baseEnd_1896507] using wordTrace_append hprefix tailTrace_1896507
  have hstable : (prefixWord ++ tailWord_1896507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896507).length < 2 ^ (prefixWord ++ tailWord_1896507).sum := by decide
  have hdescent : baseEnd_1896507 < baseStart_1896507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896521 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 1, 2, 2]
def baseStart_1896521 : Nat := 118140960795 + 1896521 * 2 ^ 59
def prefixEnd_1896521 : Nat := 4983230072969 + 3 ^ 40 * 1896521 * 2
def baseEnd_1896521 : Nat := 973826844345679586565565

theorem tailTrace_1896521 : CollatzResearch.WordTrace tailWord_1896521 prefixEnd_1896521 973826844345679586565565 := by
  unfold tailWord_1896521
  simp only [CollatzResearch.WordTrace]
  refine ⟨69171803562235791844913417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46114535708157194563275611 69171803562235791844913417)
  ·
    refine ⟨51878852671676843883685063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69171803562235791844913417 51878852671676843883685063)
    ·
      refine ⟨77818279007515265825527595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51878852671676843883685063 77818279007515265825527595)
      ·
        refine ⟨116727418511272898738291393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77818279007515265825527595 116727418511272898738291393)
        ·
          refine ⟨87545563883454674053718545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116727418511272898738291393 87545563883454674053718545)
          ·
            refine ⟨65659172912591005540288909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87545563883454674053718545 65659172912591005540288909)
            ·
              refine ⟨24622189842221627077608341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65659172912591005540288909 24622189842221627077608341)
              ·
                refine ⟨1154165148854138769262891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24622189842221627077608341 1154165148854138769262891)
                ·
                  refine ⟨1731247723281208153894337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154165148854138769262891 1731247723281208153894337)
                  ·
                    refine ⟨1298435792460906115420753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1731247723281208153894337 1298435792460906115420753)
                    ·
                      refine ⟨973826844345679586565565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298435792460906115420753 973826844345679586565565)
                      ·
                        rfl

theorem cell23_1896521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 1, 2, 2].length) (baseStart_1896521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896521 prefixEnd_1896521 := by exact prefixLift 1896521
  have htrace : WordTrace (prefixWord ++ tailWord_1896521) baseStart_1896521 baseEnd_1896521 := by
    simpa [prefixWord, tailWord_1896521, baseEnd_1896521] using wordTrace_append hprefix tailTrace_1896521
  have hstable : (prefixWord ++ tailWord_1896521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896521).length < 2 ^ (prefixWord ++ tailWord_1896521).sum := by decide
  have hdescent : baseEnd_1896521 < baseStart_1896521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896541 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 3]
def baseStart_1896541 : Nat := 118140960795 + 1896541 * 2 ^ 59
def prefixEnd_1896541 : Nat := 4983230072969 + 3 ^ 40 * 1896541 * 2
def baseEnd_1896541 : Nat := 973837113958769508315473

theorem tailTrace_1896541 : CollatzResearch.WordTrace tailWord_1896541 prefixEnd_1896541 973837113958769508315473 := by
  unfold tailWord_1896541
  simp only [CollatzResearch.WordTrace]
  refine ⟨69172533022163335260641477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46115022014775556840427651 69172533022163335260641477)
  ·
    refine ⟨12969849941655625361370277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69172533022163335260641477 12969849941655625361370277)
    ·
      refine ⟨2431846864060429755256927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12969849941655625361370277 2431846864060429755256927)
      ·
        refine ⟨3647770296090644632885391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431846864060429755256927 3647770296090644632885391)
        ·
          refine ⟨5471655444135966949328087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647770296090644632885391 5471655444135966949328087)
          ·
            refine ⟨8207483166203950423992131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471655444135966949328087 8207483166203950423992131)
            ·
              refine ⟨12311224749305925635988197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207483166203950423992131 12311224749305925635988197)
              ·
                refine ⟨2308354640494861056747787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12311224749305925635988197 2308354640494861056747787)
                ·
                  refine ⟨3462531960742291585121681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308354640494861056747787 3462531960742291585121681)
                  ·
                    refine ⟨2596898970556718688841261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3462531960742291585121681 2596898970556718688841261)
                    ·
                      refine ⟨973837113958769508315473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2596898970556718688841261 973837113958769508315473)
                      ·
                        rfl

theorem cell23_1896541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_1896541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896541 prefixEnd_1896541 := by exact prefixLift 1896541
  have htrace : WordTrace (prefixWord ++ tailWord_1896541) baseStart_1896541 baseEnd_1896541 := by
    simpa [prefixWord, tailWord_1896541, baseEnd_1896541] using wordTrace_append hprefix tailTrace_1896541
  have hstable : (prefixWord ++ tailWord_1896541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896541).length < 2 ^ (prefixWord ++ tailWord_1896541).sum := by decide
  have hdescent : baseEnd_1896541 < baseStart_1896541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896615 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 1, 3, 2]
def baseStart_1896615 : Nat := 118140960795 + 1896615 * 2 ^ 59
def prefixEnd_1896615 : Nat := 4983230072969 + 3 ^ 40 * 1896615 * 2
def baseEnd_1896615 : Nat := 973875111527202218790133

theorem tailTrace_1896615 : CollatzResearch.WordTrace tailWord_1896615 prefixEnd_1896615 973875111527202218790133 := by
  unfold tailWord_1896615
  simp only [CollatzResearch.WordTrace]
  refine ⟨69175232023895245898835299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46116821349263497265890199 69175232023895245898835299)
  ·
    refine ⟨103762848035842868848252949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69175232023895245898835299 103762848035842868848252949)
    ·
      refine ⟨4863883501680134477261857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103762848035842868848252949 4863883501680134477261857)
      ·
        refine ⟨3647912626260100857946393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4863883501680134477261857 3647912626260100857946393)
        ·
          refine ⟨2735934469695075643459795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3647912626260100857946393 2735934469695075643459795)
          ·
            refine ⟨4103901704542613465189693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735934469695075643459795 4103901704542613465189693)
            ·
              refine ⟨1538963139203480049446135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4103901704542613465189693 1538963139203480049446135)
              ·
                refine ⟨2308444708805220074169203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1538963139203480049446135 2308444708805220074169203)
                ·
                  refine ⟨3462667063207830111253805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308444708805220074169203 3462667063207830111253805)
                  ·
                    refine ⟨1298500148702936291720177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3462667063207830111253805 1298500148702936291720177)
                    ·
                      refine ⟨973875111527202218790133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298500148702936291720177 973875111527202218790133)
                      ·
                        rfl

theorem cell23_1896615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_1896615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896615 prefixEnd_1896615 := by exact prefixLift 1896615
  have htrace : WordTrace (prefixWord ++ tailWord_1896615) baseStart_1896615 baseEnd_1896615 := by
    simpa [prefixWord, tailWord_1896615, baseEnd_1896615] using wordTrace_append hprefix tailTrace_1896615
  have hstable : (prefixWord ++ tailWord_1896615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896615).length < 2 ^ (prefixWord ++ tailWord_1896615).sum := by decide
  have hdescent : baseEnd_1896615 < baseStart_1896615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896620 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 8]
def baseStart_1896620 : Nat := 118140960795 + 1896620 * 2 ^ 59
def prefixEnd_1896620 : Nat := 4983230072969 + 3 ^ 40 * 1896620 * 2
def baseEnd_1896620 : Nat := 973877678930474699227609

theorem tailTrace_1896620 : CollatzResearch.WordTrace tailWord_1896620 prefixEnd_1896620 973877678930474699227609 := by
  unfold tailWord_1896620
  simp only [CollatzResearch.WordTrace]
  refine ⟨34587707194438565876383657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46116942925918087835178209 34587707194438565876383657)
  ·
    refine ⟨25940780395828924407287743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34587707194438565876383657 25940780395828924407287743)
    ·
      refine ⟨38911170593743386610931615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25940780395828924407287743 38911170593743386610931615)
      ·
        refine ⟨58366755890615079916397423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38911170593743386610931615 58366755890615079916397423)
        ·
          refine ⟨87550133835922619874596135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58366755890615079916397423 87550133835922619874596135)
          ·
            refine ⟨131325200753883929811894203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87550133835922619874596135 131325200753883929811894203)
            ·
              refine ⟨196987801130825894717841305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131325200753883929811894203 196987801130825894717841305)
              ·
                refine ⟨147740850848119421038380979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196987801130825894717841305 147740850848119421038380979)
                ·
                  refine ⟨221611276272179131557571469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 147740850848119421038380979 221611276272179131557571469)
                  ·
                    refine ⟨83104228602067174334089301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 221611276272179131557571469 83104228602067174334089301)
                    ·
                      refine ⟨973877678930474699227609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 83104228602067174334089301 973877678930474699227609)
                      ·
                        rfl

theorem cell23_1896620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_1896620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896620 prefixEnd_1896620 := by exact prefixLift 1896620
  have htrace : WordTrace (prefixWord ++ tailWord_1896620) baseStart_1896620 baseEnd_1896620 := by
    simpa [prefixWord, tailWord_1896620, baseEnd_1896620] using wordTrace_append hprefix tailTrace_1896620
  have hstable : (prefixWord ++ tailWord_1896620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896620).length < 2 ^ (prefixWord ++ tailWord_1896620).sum := by decide
  have hdescent : baseEnd_1896620 < baseStart_1896620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896627 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 3]
def baseStart_1896627 : Nat := 118140960795 + 1896627 * 2 ^ 59
def prefixEnd_1896627 : Nat := 4983230072969 + 3 ^ 40 * 1896627 * 2
def baseEnd_1896627 : Nat := 973881273295056171840077

theorem tailTrace_1896627 : CollatzResearch.WordTrace tailWord_1896627 prefixEnd_1896627 973881273295056171840077 := by
  unfold tailWord_1896627
  simp only [CollatzResearch.WordTrace]
  refine ⟨69175669699851771948272135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46117113133234514632181423 69175669699851771948272135)
  ·
    refine ⟨103763504549777657922408203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69175669699851771948272135 103763504549777657922408203)
    ·
      refine ⟨155645256824666486883612305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103763504549777657922408203 155645256824666486883612305)
      ·
        refine ⟨116733942618499865162709229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155645256824666486883612305 116733942618499865162709229)
        ·
          refine ⟨43775228481937449436015961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116733942618499865162709229 43775228481937449436015961)
          ·
            refine ⟨32831421361453087077011971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43775228481937449436015961 32831421361453087077011971)
            ·
              refine ⟨49247132042179630615517957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32831421361453087077011971 49247132042179630615517957)
              ·
                refine ⟨9233837257908680740409617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49247132042179630615517957 9233837257908680740409617)
                ·
                  refine ⟨6925377943431510555307213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9233837257908680740409617 6925377943431510555307213)
                  ·
                    refine ⟨2597016728786816458240205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6925377943431510555307213 2597016728786816458240205)
                    ·
                      refine ⟨973881273295056171840077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597016728786816458240205 973881273295056171840077)
                      ·
                        rfl

theorem cell23_1896627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 3].length) (baseStart_1896627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896627 prefixEnd_1896627 := by exact prefixLift 1896627
  have htrace : WordTrace (prefixWord ++ tailWord_1896627) baseStart_1896627 baseEnd_1896627 := by
    simpa [prefixWord, tailWord_1896627, baseEnd_1896627] using wordTrace_append hprefix tailTrace_1896627
  have hstable : (prefixWord ++ tailWord_1896627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896627).length < 2 ^ (prefixWord ++ tailWord_1896627).sum := by decide
  have hdescent : baseEnd_1896627 < baseStart_1896627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896641 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1896641 : Nat := 118140960795 + 1896641 * 2 ^ 59
def prefixEnd_1896641 : Nat := 4983230072969 + 3 ^ 40 * 1896641 * 2
def baseEnd_1896641 : Nat := 973888462024219117065013

theorem tailTrace_1896641 : CollatzResearch.WordTrace tailWord_1896641 prefixEnd_1896641 973888462024219117065013 := by
  unfold tailWord_1896641
  simp only [CollatzResearch.WordTrace]
  refine ⟨69176180321801052339281777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46117453547867368226187851 69176180321801052339281777)
  ·
    refine ⟨51882135241350789254461333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69176180321801052339281777 51882135241350789254461333)
    ·
      refine ⟨2431975089438318246302875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51882135241350789254461333 2431975089438318246302875)
      ·
        refine ⟨3647962634157477369454313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431975089438318246302875 3647962634157477369454313)
        ·
          refine ⟨2735971975618108027090735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3647962634157477369454313 2735971975618108027090735)
          ·
            refine ⟨4103957963427162040636103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2735971975618108027090735 4103957963427162040636103)
            ·
              refine ⟨6155936945140743060954155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4103957963427162040636103 6155936945140743060954155)
              ·
                refine ⟨9233905417711114591431233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6155936945140743060954155 9233905417711114591431233)
                ·
                  refine ⟨6925429063283335943573425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9233905417711114591431233 6925429063283335943573425)
                  ·
                    refine ⟨5194071797462501957680069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6925429063283335943573425 5194071797462501957680069)
                    ·
                      refine ⟨973888462024219117065013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5194071797462501957680069 973888462024219117065013)
                      ·
                        rfl

theorem cell23_1896641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1896641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896641 prefixEnd_1896641 := by exact prefixLift 1896641
  have htrace : WordTrace (prefixWord ++ tailWord_1896641) baseStart_1896641 baseEnd_1896641 := by
    simpa [prefixWord, tailWord_1896641, baseEnd_1896641] using wordTrace_append hprefix tailTrace_1896641
  have hstable : (prefixWord ++ tailWord_1896641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896641).length < 2 ^ (prefixWord ++ tailWord_1896641).sum := by decide
  have hdescent : baseEnd_1896641 < baseStart_1896641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896644 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1896644 : Nat := 118140960795 + 1896644 * 2 ^ 59
def prefixEnd_1896644 : Nat := 4983230072969 + 3 ^ 40 * 1896644 * 2
def baseEnd_1896644 : Nat := 973890002466182605327499

theorem tailTrace_1896644 : CollatzResearch.WordTrace tailWord_1896644 prefixEnd_1896644 973890002466182605327499 := by
  unfold tailWord_1896644
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588144870395091925820493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46117526493860122567760657 34588144870395091925820493)
  ·
    refine ⟨12970554326398159472182685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34588144870395091925820493 12970554326398159472182685)
    ·
      refine ⟨4863957872399309802068507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12970554326398159472182685 4863957872399309802068507)
      ·
        refine ⟨7295936808598964703102761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4863957872399309802068507 7295936808598964703102761)
        ·
          refine ⟨5471952606449223527327071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7295936808598964703102761 5471952606449223527327071)
          ·
            refine ⟨8207928909673835290990607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5471952606449223527327071 8207928909673835290990607)
            ·
              refine ⟨12311893364510752936485911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8207928909673835290990607 12311893364510752936485911)
              ·
                refine ⟨18467840046766129404728867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12311893364510752936485911 18467840046766129404728867)
                ·
                  refine ⟨27701760070149194107093301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18467840046766129404728867 27701760070149194107093301)
                  ·
                    refine ⟨2597040006576486947539997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27701760070149194107093301 2597040006576486947539997)
                    ·
                      refine ⟨973890002466182605327499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597040006576486947539997 973890002466182605327499)
                      ·
                        rfl

theorem cell23_1896644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1896644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896644 prefixEnd_1896644 := by exact prefixLift 1896644
  have htrace : WordTrace (prefixWord ++ tailWord_1896644) baseStart_1896644 baseEnd_1896644 := by
    simpa [prefixWord, tailWord_1896644, baseEnd_1896644] using wordTrace_append hprefix tailTrace_1896644
  have hstable : (prefixWord ++ tailWord_1896644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896644).length < 2 ^ (prefixWord ++ tailWord_1896644).sum := by decide
  have hdescent : baseEnd_1896644 < baseStart_1896644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896664 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 2, 5]
def baseStart_1896664 : Nat := 118140960795 + 1896664 * 2 ^ 59
def prefixEnd_1896664 : Nat := 4983230072969 + 3 ^ 40 * 1896664 * 2
def baseEnd_1896664 : Nat := 324633424026424175692469

theorem tailTrace_1896664 : CollatzResearch.WordTrace tailWord_1896664 prefixEnd_1896664 324633424026424175692469 := by
  unfold tailWord_1896664
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588509600358863633684523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46118012800478484844912697 34588509600358863633684523)
  ·
    refine ⟨51882764400538295450526785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34588509600358863633684523 51882764400538295450526785)
    ·
      refine ⟨38912073300403721587895089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51882764400538295450526785 38912073300403721587895089)
      ·
        refine ⟨29184054975302791190921317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38912073300403721587895089 29184054975302791190921317)
        ·
          refine ⟨5472010307869273348297747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29184054975302791190921317 5472010307869273348297747)
          ·
            refine ⟨8208015461803910022446621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472010307869273348297747 8208015461803910022446621)
            ·
              refine ⟨3078005798176466258417483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8208015461803910022446621 3078005798176466258417483)
              ·
                refine ⟨4617008697264699387626225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078005798176466258417483 4617008697264699387626225)
                ·
                  refine ⟨3462756522948524540719669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4617008697264699387626225 3462756522948524540719669)
                  ·
                    refine ⟨324633424026424175692469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3462756522948524540719669 324633424026424175692469)
                    ·
                      rfl

theorem cell23_1896664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 2, 5].length) (baseStart_1896664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896664 prefixEnd_1896664 := by exact prefixLift 1896664
  have htrace : WordTrace (prefixWord ++ tailWord_1896664) baseStart_1896664 baseEnd_1896664 := by
    simpa [prefixWord, tailWord_1896664, baseEnd_1896664] using wordTrace_append hprefix tailTrace_1896664
  have hstable : (prefixWord ++ tailWord_1896664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896664).length < 2 ^ (prefixWord ++ tailWord_1896664).sum := by decide
  have hdescent : baseEnd_1896664 < baseStart_1896664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896684 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 4, 4, 2]
def baseStart_1896684 : Nat := 118140960795 + 1896684 * 2 ^ 59
def prefixEnd_1896684 : Nat := 4983230072969 + 3 ^ 40 * 1896684 * 2
def baseEnd_1896684 : Nat := 973910541692362448827315

theorem tailTrace_1896684 : CollatzResearch.WordTrace tailWord_1896684 prefixEnd_1896684 973910541692362448827315 := by
  unfold tailWord_1896684
  simp only [CollatzResearch.WordTrace]
  refine ⟨34588874330322635341548553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46118499107096847122064737 34588874330322635341548553)
  ·
    refine ⟨25941655747741976506161415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34588874330322635341548553 25941655747741976506161415)
    ·
      refine ⟨38912483621612964759242123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25941655747741976506161415 38912483621612964759242123)
      ·
        refine ⟨58368725432419447138863185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38912483621612964759242123 58368725432419447138863185)
        ·
          refine ⟨43776544074314585354147389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58368725432419447138863185 43776544074314585354147389)
          ·
            refine ⟨16416204027867969507805271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43776544074314585354147389 16416204027867969507805271)
            ·
              refine ⟨24624306041801954261707907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16416204027867969507805271 24624306041801954261707907)
              ·
                refine ⟨36936459062702931392561861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24624306041801954261707907 36936459062702931392561861)
                ·
                  refine ⟨6925586074256799636105349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36936459062702931392561861 6925586074256799636105349)
                  ·
                    refine ⟨1298547388923149931769753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6925586074256799636105349 1298547388923149931769753)
                    ·
                      refine ⟨973910541692362448827315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298547388923149931769753 973910541692362448827315)
                      ·
                        rfl

theorem cell23_1896684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 4, 2].length) (baseStart_1896684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896684 prefixEnd_1896684 := by exact prefixLift 1896684
  have htrace : WordTrace (prefixWord ++ tailWord_1896684) baseStart_1896684 baseEnd_1896684 := by
    simpa [prefixWord, tailWord_1896684, baseEnd_1896684] using wordTrace_append hprefix tailTrace_1896684
  have hstable : (prefixWord ++ tailWord_1896684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896684).length < 2 ^ (prefixWord ++ tailWord_1896684).sum := by decide
  have hdescent : baseEnd_1896684 < baseStart_1896684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896751 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 3]
def baseStart_1896751 : Nat := 118140960795 + 1896751 * 2 ^ 59
def prefixEnd_1896751 : Nat := 4983230072969 + 3 ^ 40 * 1896751 * 2
def baseEnd_1896751 : Nat := 973944944896213686689507

theorem tailTrace_1896751 : CollatzResearch.WordTrace tailWord_1896751 prefixEnd_1896751 973944944896213686689507 := by
  unfold tailWord_1896751
  simp only [CollatzResearch.WordTrace]
  refine ⟨69180192351402541125786107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46120128234268360750524071 69180192351402541125786107)
  ·
    refine ⟨103770288527103811688679161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69180192351402541125786107 103770288527103811688679161)
    ·
      refine ⟨77827716395327858766509371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103770288527103811688679161 77827716395327858766509371)
      ·
        refine ⟨116741574592991788149764057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77827716395327858766509371 116741574592991788149764057)
        ·
          refine ⟨87556180944743841112323043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116741574592991788149764057 87556180944743841112323043)
          ·
            refine ⟨131334271417115761668484565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87556180944743841112323043 131334271417115761668484565)
            ·
              refine ⟨3078146986338650664105107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 131334271417115761668484565 3078146986338650664105107)
              ·
                refine ⟨4617220479507975996157661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078146986338650664105107 4617220479507975996157661)
                ·
                  refine ⟨1731457679815490998559123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4617220479507975996157661 1731457679815490998559123)
                  ·
                    refine ⟨2597186519723236497838685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1731457679815490998559123 2597186519723236497838685)
                    ·
                      refine ⟨973944944896213686689507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597186519723236497838685 973944944896213686689507)
                      ·
                        rfl

theorem cell23_1896751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_1896751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896751 prefixEnd_1896751 := by exact prefixLift 1896751
  have htrace : WordTrace (prefixWord ++ tailWord_1896751) baseStart_1896751 baseEnd_1896751 := by
    simpa [prefixWord, tailWord_1896751, baseEnd_1896751] using wordTrace_append hprefix tailTrace_1896751
  have hstable : (prefixWord ++ tailWord_1896751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896751).length < 2 ^ (prefixWord ++ tailWord_1896751).sum := by decide
  have hdescent : baseEnd_1896751 < baseStart_1896751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896784 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 1, 6]
def baseStart_1896784 : Nat := 118140960795 + 1896784 * 2 ^ 59
def prefixEnd_1896784 : Nat := 4983230072969 + 3 ^ 40 * 1896784 * 2
def baseEnd_1896784 : Nat := 324653963252604019192285

theorem tailTrace_1896784 : CollatzResearch.WordTrace tailWord_1896784 prefixEnd_1896784 324653963252604019192285 := by
  unfold tailWord_1896784
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590697980141493880868703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46120930640188658507824937 34590697980141493880868703)
  ·
    refine ⟨51886046970212240821303055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34590697980141493880868703 51886046970212240821303055)
    ·
      refine ⟨77829070455318361231954583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51886046970212240821303055 77829070455318361231954583)
      ·
        refine ⟨116743605682977541847931875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77829070455318361231954583 116743605682977541847931875)
        ·
          refine ⟨175115408524466312771897813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116743605682977541847931875 175115408524466312771897813)
          ·
            refine ⟨4104267387292179205591355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 175115408524466312771897813 4104267387292179205591355)
            ·
              refine ⟨6156401080938268808387033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104267387292179205591355 6156401080938268808387033)
              ·
                refine ⟨4617300810703701606290275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156401080938268808387033 4617300810703701606290275)
                ·
                  refine ⟨6925951216055552409435413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617300810703701606290275 6925951216055552409435413)
                  ·
                    refine ⟨324653963252604019192285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6925951216055552409435413 324653963252604019192285)
                    ·
                      rfl

theorem cell23_1896784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 1, 6].length) (baseStart_1896784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896784 prefixEnd_1896784 := by exact prefixLift 1896784
  have htrace : WordTrace (prefixWord ++ tailWord_1896784) baseStart_1896784 baseEnd_1896784 := by
    simpa [prefixWord, tailWord_1896784, baseEnd_1896784] using wordTrace_append hprefix tailTrace_1896784
  have hstable : (prefixWord ++ tailWord_1896784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896784).length < 2 ^ (prefixWord ++ tailWord_1896784).sum := by decide
  have hdescent : baseEnd_1896784 < baseStart_1896784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896787 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6]
def baseStart_1896787 : Nat := 118140960795 + 1896787 * 2 ^ 59
def prefixEnd_1896787 : Nat := 4983230072969 + 3 ^ 40 * 1896787 * 2
def baseEnd_1896787 : Nat := 973963430199775545839341

theorem tailTrace_1896787 : CollatzResearch.WordTrace tailWord_1896787 prefixEnd_1896787 973963430199775545839341 := by
  unfold tailWord_1896787
  simp only [CollatzResearch.WordTrace]
  refine ⟨69181505379272119274096615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46121003586181412849397743 69181505379272119274096615)
  ·
    refine ⟨103772258068908178911144923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69181505379272119274096615 103772258068908178911144923)
    ·
      refine ⟨155658387103362268366717385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103772258068908178911144923 155658387103362268366717385)
      ·
        refine ⟨116743790327521701275038039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155658387103362268366717385 116743790327521701275038039)
        ·
          refine ⟨175115685491282551912557059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116743790327521701275038039 175115685491282551912557059)
          ·
            refine ⟨262673528236923827868835589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175115685491282551912557059 262673528236923827868835589)
            ·
              refine ⟨49251286544423217725406673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 262673528236923827868835589 49251286544423217725406673)
              ·
                refine ⟨36938464908317413294055005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49251286544423217725406673 36938464908317413294055005)
                ·
                  refine ⟨13851924340619029985270627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36938464908317413294055005 13851924340619029985270627)
                  ·
                    refine ⟨20777886510928544977905941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13851924340619029985270627 20777886510928544977905941)
                    ·
                      refine ⟨973963430199775545839341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20777886510928544977905941 973963430199775545839341)
                      ·
                        rfl

theorem cell23_1896787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 6].length) (baseStart_1896787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896787 prefixEnd_1896787 := by exact prefixLift 1896787
  have htrace : WordTrace (prefixWord ++ tailWord_1896787) baseStart_1896787 baseEnd_1896787 := by
    simpa [prefixWord, tailWord_1896787, baseEnd_1896787] using wordTrace_append hprefix tailTrace_1896787
  have hstable : (prefixWord ++ tailWord_1896787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896787).length < 2 ^ (prefixWord ++ tailWord_1896787).sum := by decide
  have hdescent : baseEnd_1896787 < baseStart_1896787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896788 : List Nat := [2, 4, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1896788 : Nat := 118140960795 + 1896788 * 2 ^ 59
def prefixEnd_1896788 : Nat := 4983230072969 + 3 ^ 40 * 1896788 * 2
def baseEnd_1896788 : Nat := 324654647893476680642279

theorem tailTrace_1896788 : CollatzResearch.WordTrace tailWord_1896788 prefixEnd_1896788 324654647893476680642279 := by
  unfold tailWord_1896788
  simp only [CollatzResearch.WordTrace]
  refine ⟨34590770926134248222441509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46121027901512330963255345 34590770926134248222441509)
  ·
    refine ⟨6485769548650171541707783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34590770926134248222441509 6485769548650171541707783)
    ·
      refine ⟨9728654322975257312561675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6485769548650171541707783 9728654322975257312561675)
      ·
        refine ⟨14592981484462885968842513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9728654322975257312561675 14592981484462885968842513)
        ·
          refine ⟨10944736113347164476631885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14592981484462885968842513 10944736113347164476631885)
          ·
            refine ⟨4104276042505186678736957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10944736113347164476631885 4104276042505186678736957)
            ·
              refine ⟨1539103515939445004526359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4104276042505186678736957 1539103515939445004526359)
              ·
                refine ⟨2308655273909167506789539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539103515939445004526359 2308655273909167506789539)
                ·
                  refine ⟨3462982910863751260184309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308655273909167506789539 3462982910863751260184309)
                  ·
                    refine ⟨324654647893476680642279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3462982910863751260184309 324654647893476680642279)
                    ·
                      rfl

theorem cell23_1896788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1896788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896788 prefixEnd_1896788 := by exact prefixLift 1896788
  have htrace : WordTrace (prefixWord ++ tailWord_1896788) baseStart_1896788 baseEnd_1896788 := by
    simpa [prefixWord, tailWord_1896788, baseEnd_1896788] using wordTrace_append hprefix tailTrace_1896788
  have hstable : (prefixWord ++ tailWord_1896788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896788).length < 2 ^ (prefixWord ++ tailWord_1896788).sum := by decide
  have hdescent : baseEnd_1896788 < baseStart_1896788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896802 : List Nat := [3, 3, 2, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_1896802 : Nat := 118140960795 + 1896802 * 2 ^ 59
def prefixEnd_1896802 : Nat := 4983230072969 + 3 ^ 40 * 1896802 * 2
def baseEnd_1896802 : Nat := 973971132409592987151773

theorem tailTrace_1896802 : CollatzResearch.WordTrace tailWord_1896802 prefixEnd_1896802 973971132409592987151773 := by
  unfold tailWord_1896802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295513118554444208973165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46121368316145184557261773 17295513118554444208973165)
  ·
    refine ⟨6485817419457916578364937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17295513118554444208973165 6485817419457916578364937)
    ·
      refine ⟨4864363064593437433773703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6485817419457916578364937 4864363064593437433773703)
      ·
        refine ⟨7296544596890156150660555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864363064593437433773703 7296544596890156150660555)
        ·
          refine ⟨10944816895335234225990833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296544596890156150660555 10944816895335234225990833)
          ·
            refine ⟨8208612671501425669493125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10944816895335234225990833 8208612671501425669493125)
            ·
              refine ⟨1539114875906517313029961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8208612671501425669493125 1539114875906517313029961)
              ·
                refine ⟨1154336156929887984772471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539114875906517313029961 1154336156929887984772471)
                ·
                  refine ⟨1731504235394831977158707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154336156929887984772471 1731504235394831977158707)
                  ·
                    refine ⟨2597256353092247965738061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1731504235394831977158707 2597256353092247965738061)
                    ·
                      refine ⟨973971132409592987151773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597256353092247965738061 973971132409592987151773)
                      ·
                        rfl

theorem cell23_1896802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_1896802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896802 prefixEnd_1896802 := by exact prefixLift 1896802
  have htrace : WordTrace (prefixWord ++ tailWord_1896802) baseStart_1896802 baseEnd_1896802 := by
    simpa [prefixWord, tailWord_1896802, baseEnd_1896802] using wordTrace_append hprefix tailTrace_1896802
  have hstable : (prefixWord ++ tailWord_1896802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896802).length < 2 ^ (prefixWord ++ tailWord_1896802).sum := by decide
  have hdescent : baseEnd_1896802 < baseStart_1896802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896804 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 3, 2, 4]
def baseStart_1896804 : Nat := 118140960795 + 1896804 * 2 ^ 59
def prefixEnd_1896804 : Nat := 4983230072969 + 3 ^ 40 * 1896804 * 2
def baseEnd_1896804 : Nat := 973972159370901979326763

theorem tailTrace_1896804 : CollatzResearch.WordTrace tailWord_1896804 prefixEnd_1896804 973972159370901979326763 := by
  unfold tailWord_1896804
  simp only [CollatzResearch.WordTrace]
  refine ⟨34591062710105265588732733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46121416946807020784976977 34591062710105265588732733)
  ·
    refine ⟨12971648516289474595774775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34591062710105265588732733 12971648516289474595774775)
    ·
      refine ⟨19457472774434211893662163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12971648516289474595774775 19457472774434211893662163)
      ·
        refine ⟨29186209161651317840493245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19457472774434211893662163 29186209161651317840493245)
        ·
          refine ⟨10944828435619244190184967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29186209161651317840493245 10944828435619244190184967)
          ·
            refine ⟨16417242653428866285277451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10944828435619244190184967 16417242653428866285277451)
            ·
              refine ⟨24625863980143299427916177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16417242653428866285277451 24625863980143299427916177)
              ·
                refine ⟨18469397985107474570937133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24625863980143299427916177 18469397985107474570937133)
                ·
                  refine ⟨6926024244415302964101425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18469397985107474570937133 6926024244415302964101425)
                  ·
                    refine ⟨5194518183311477223076069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6926024244415302964101425 5194518183311477223076069)
                    ·
                      refine ⟨973972159370901979326763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5194518183311477223076069 973972159370901979326763)
                      ·
                        rfl

theorem cell23_1896804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_1896804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896804 prefixEnd_1896804 := by exact prefixLift 1896804
  have htrace : WordTrace (prefixWord ++ tailWord_1896804) baseStart_1896804 baseEnd_1896804 := by
    simpa [prefixWord, tailWord_1896804, baseEnd_1896804] using wordTrace_append hprefix tailTrace_1896804
  have hstable : (prefixWord ++ tailWord_1896804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896804).length < 2 ^ (prefixWord ++ tailWord_1896804).sum := by decide
  have hdescent : baseEnd_1896804 < baseStart_1896804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896821 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_1896821 : Nat := 118140960795 + 1896821 * 2 ^ 59
def prefixEnd_1896821 : Nat := 4983230072969 + 3 ^ 40 * 1896821 * 2
def baseEnd_1896821 : Nat := 973980888542028412814185

theorem tailTrace_1896821 : CollatzResearch.WordTrace tailWord_1896821 prefixEnd_1896821 973980888542028412814185 := by
  unfold tailWord_1896821
  simp only [CollatzResearch.WordTrace]
  refine ⟨69182745461148943080834317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46121830307432628720556211 69182745461148943080834317)
  ·
    refine ⟨25943529547930853655312869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69182745461148943080834317 25943529547930853655312869)
    ·
      refine ⟨4864411790237035060371163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25943529547930853655312869 4864411790237035060371163)
      ·
        refine ⟨7296617685355552590556745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864411790237035060371163 7296617685355552590556745)
        ·
          refine ⟨5472463264016664442917559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7296617685355552590556745 5472463264016664442917559)
          ·
            refine ⟨8208694896024996664376339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472463264016664442917559 8208694896024996664376339)
            ·
              refine ⟨12313042344037494996564509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8208694896024996664376339 12313042344037494996564509)
              ·
                refine ⟨4617390879014060623711691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12313042344037494996564509 4617390879014060623711691)
                ·
                  refine ⟨6926086318521090935567537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617390879014060623711691 6926086318521090935567537)
                  ·
                    refine ⟨5194564738890818201675653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6926086318521090935567537 5194564738890818201675653)
                    ·
                      refine ⟨973980888542028412814185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5194564738890818201675653 973980888542028412814185)
                      ·
                        rfl

theorem cell23_1896821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_1896821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896821 prefixEnd_1896821 := by exact prefixLift 1896821
  have htrace : WordTrace (prefixWord ++ tailWord_1896821) baseStart_1896821 baseEnd_1896821 := by
    simpa [prefixWord, tailWord_1896821, baseEnd_1896821] using wordTrace_append hprefix tailTrace_1896821
  have hstable : (prefixWord ++ tailWord_1896821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896821).length < 2 ^ (prefixWord ++ tailWord_1896821).sum := by decide
  have hdescent : baseEnd_1896821 < baseStart_1896821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896841 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_1896841 : Nat := 118140960795 + 1896841 * 2 ^ 59
def prefixEnd_1896841 : Nat := 4983230072969 + 3 ^ 40 * 1896841 * 2
def baseEnd_1896841 : Nat := 973991158155118334564093

theorem tailTrace_1896841 : CollatzResearch.WordTrace tailWord_1896841 prefixEnd_1896841 973991158155118334564093 := by
  unfold tailWord_1896841
  simp only [CollatzResearch.WordTrace]
  refine ⟨69183474921076486496562377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46122316614050990997708251 69183474921076486496562377)
  ·
    refine ⟨51887606190807364872421783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69183474921076486496562377 51887606190807364872421783)
    ·
      refine ⟨77831409286211047308632675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51887606190807364872421783 77831409286211047308632675)
      ·
        refine ⟨116747113929316570962949013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77831409286211047308632675 116747113929316570962949013)
        ·
          refine ⟨5472520965436714263888235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 116747113929316570962949013 5472520965436714263888235)
          ·
            refine ⟨8208781448155071395832353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472520965436714263888235 8208781448155071395832353)
            ·
              refine ⟨6156586086116303546874265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8208781448155071395832353 6156586086116303546874265)
              ·
                refine ⟨4617439564587227660155699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6156586086116303546874265 4617439564587227660155699)
                ·
                  refine ⟨6926159346880841490233549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617439564587227660155699 6926159346880841490233549)
                  ·
                    refine ⟨2597309755080315558837581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6926159346880841490233549 2597309755080315558837581)
                    ·
                      refine ⟨973991158155118334564093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597309755080315558837581 973991158155118334564093)
                      ·
                        rfl

theorem cell23_1896841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_1896841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896841 prefixEnd_1896841 := by exact prefixLift 1896841
  have htrace : WordTrace (prefixWord ++ tailWord_1896841) baseStart_1896841 baseEnd_1896841 := by
    simpa [prefixWord, tailWord_1896841, baseEnd_1896841] using wordTrace_append hprefix tailTrace_1896841
  have hstable : (prefixWord ++ tailWord_1896841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896841).length < 2 ^ (prefixWord ++ tailWord_1896841).sum := by decide
  have hdescent : baseEnd_1896841 < baseStart_1896841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896842 : List Nat := [3, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_1896842 : Nat := 118140960795 + 1896842 * 2 ^ 59
def prefixEnd_1896842 : Nat := 4983230072969 + 3 ^ 40 * 1896842 * 2
def baseEnd_1896842 : Nat := 973991671635772830651589

theorem tailTrace_1896842 : CollatzResearch.WordTrace tailWord_1896842 prefixEnd_1896842 973991671635772830651589 := by
  unfold tailWord_1896842
  simp only [CollatzResearch.WordTrace]
  refine ⟨17295877848518215916837195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46122340929381909111565853 17295877848518215916837195)
  ·
    refine ⟨25943816772777323875255793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17295877848518215916837195 25943816772777323875255793)
    ·
      refine ⟨19457862579582992906441845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25943816772777323875255793 19457862579582992906441845)
      ·
        refine ⟨1824174616835905584978923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19457862579582992906441845 1824174616835905584978923)
        ·
          refine ⟨2736261925253858377468385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824174616835905584978923 2736261925253858377468385)
          ·
            refine ⟨2052196443940393783101289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736261925253858377468385 2052196443940393783101289)
            ·
              refine ⟨1539147332955295337325967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052196443940393783101289 1539147332955295337325967)
              ·
                refine ⟨2308720999432943005988951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539147332955295337325967 2308720999432943005988951)
                ·
                  refine ⟨3463081499149414508983427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2308720999432943005988951 3463081499149414508983427)
                  ·
                    refine ⟨5194622248724121763475141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463081499149414508983427 5194622248724121763475141)
                    ·
                      refine ⟨973991671635772830651589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5194622248724121763475141 973991671635772830651589)
                      ·
                        rfl

theorem cell23_1896842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_1896842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896842 prefixEnd_1896842 := by exact prefixLift 1896842
  have htrace : WordTrace (prefixWord ++ tailWord_1896842) baseStart_1896842 baseEnd_1896842 := by
    simpa [prefixWord, tailWord_1896842, baseEnd_1896842] using wordTrace_append hprefix tailTrace_1896842
  have hstable : (prefixWord ++ tailWord_1896842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896842).length < 2 ^ (prefixWord ++ tailWord_1896842).sum := by decide
  have hdescent : baseEnd_1896842 < baseStart_1896842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896852 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1896852 : Nat := 118140960795 + 1896852 * 2 ^ 59
def prefixEnd_1896852 : Nat := 4983230072969 + 3 ^ 40 * 1896852 * 2
def baseEnd_1896852 : Nat := 324665602147439263842181

theorem tailTrace_1896852 : CollatzResearch.WordTrace tailWord_1896852 prefixEnd_1896852 324665602147439263842181 := by
  unfold tailWord_1896852
  simp only [CollatzResearch.WordTrace]
  refine ⟨34591938062018317687606405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46122584082691090250141873 34591938062018317687606405)
  ·
    refine ⟨6485988386628434566426201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34591938062018317687606405 6485988386628434566426201)
    ·
      refine ⟨4864491289971325924819651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6485988386628434566426201 4864491289971325924819651)
      ·
        refine ⟨7296736934956988887229477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864491289971325924819651 7296736934956988887229477)
        ·
          refine ⟨1368138175304435416355527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7296736934956988887229477 1368138175304435416355527)
          ·
            refine ⟨2052207262956653124533291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1368138175304435416355527 2052207262956653124533291)
            ·
              refine ⟨3078310894434979686799937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2052207262956653124533291 3078310894434979686799937)
              ·
                refine ⟨2308733170826234765099953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3078310894434979686799937 2308733170826234765099953)
                ·
                  refine ⟨1731549878119676073824965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2308733170826234765099953 1731549878119676073824965)
                  ·
                    refine ⟨324665602147439263842181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1731549878119676073824965 324665602147439263842181)
                    ·
                      rfl

theorem cell23_1896852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1896852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896852 prefixEnd_1896852 := by exact prefixLift 1896852
  have htrace : WordTrace (prefixWord ++ tailWord_1896852) baseStart_1896852 baseEnd_1896852 := by
    simpa [prefixWord, tailWord_1896852, baseEnd_1896852] using wordTrace_append hprefix tailTrace_1896852
  have hstable : (prefixWord ++ tailWord_1896852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896852).length < 2 ^ (prefixWord ++ tailWord_1896852).sum := by decide
  have hdescent : baseEnd_1896852 < baseStart_1896852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896858 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_1896858 : Nat := 118140960795 + 1896858 * 2 ^ 59
def prefixEnd_1896858 : Nat := 4983230072969 + 3 ^ 40 * 1896858 * 2
def baseEnd_1896858 : Nat := 973999887326244768051515

theorem tailTrace_1896858 : CollatzResearch.WordTrace tailWord_1896858 prefixEnd_1896858 973999887326244768051515 := by
  unfold tailWord_1896858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17296023740503724599982807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46122729974676598933287485 17296023740503724599982807)
  ·
    refine ⟨25944035610755586899974211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17296023740503724599982807 25944035610755586899974211)
    ·
      refine ⟨38916053416133380349961317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25944035610755586899974211 38916053416133380349961317)
      ·
        refine ⟨7296760015525008815617747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38916053416133380349961317 7296760015525008815617747)
        ·
          refine ⟨10945140023287513223426621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296760015525008815617747 10945140023287513223426621)
          ·
            refine ⟨4104427508732817458784983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10945140023287513223426621 4104427508732817458784983)
            ·
              refine ⟨6156641263099226188177475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4104427508732817458784983 6156641263099226188177475)
              ·
                refine ⟨9234961894648839282266213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6156641263099226188177475 9234961894648839282266213)
                ·
                  refine ⟨1731555355246657365424915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9234961894648839282266213 1731555355246657365424915)
                  ·
                    refine ⟨2597333032869986048137373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1731555355246657365424915 2597333032869986048137373)
                    ·
                      refine ⟨973999887326244768051515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597333032869986048137373 973999887326244768051515)
                      ·
                        rfl

theorem cell23_1896858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_1896858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896858 prefixEnd_1896858 := by exact prefixLift 1896858
  have htrace : WordTrace (prefixWord ++ tailWord_1896858) baseStart_1896858 baseEnd_1896858 := by
    simpa [prefixWord, tailWord_1896858, baseEnd_1896858] using wordTrace_append hprefix tailTrace_1896858
  have hstable : (prefixWord ++ tailWord_1896858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896858).length < 2 ^ (prefixWord ++ tailWord_1896858).sum := by decide
  have hdescent : baseEnd_1896858 < baseStart_1896858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896918 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3]
def baseStart_1896918 : Nat := 118140960795 + 1896918 * 2 ^ 59
def prefixEnd_1896918 : Nat := 4983230072969 + 3 ^ 40 * 1896918 * 2
def baseEnd_1896918 : Nat := 974030696165514533301239

theorem tailTrace_1896918 : CollatzResearch.WordTrace tailWord_1896918 prefixEnd_1896918 974030696165514533301239 := by
  unfold tailWord_1896918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324142708862345540444713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46124188894531685764743605 4324142708862345540444713)
  ·
    refine ⟨3243107031646759155333535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4324142708862345540444713 3243107031646759155333535)
    ·
      refine ⟨4864660547470138733000303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243107031646759155333535 4864660547470138733000303)
      ·
        refine ⟨7296990821205208099500455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4864660547470138733000303 7296990821205208099500455)
        ·
          refine ⟨10945486231807812149250683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7296990821205208099500455 10945486231807812149250683)
          ·
            refine ⟨16418229347711718223876025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10945486231807812149250683 16418229347711718223876025)
            ·
              refine ⟨12313672010783788667907019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16418229347711718223876025 12313672010783788667907019)
              ·
                refine ⟨18470508016175683001860529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12313672010783788667907019 18470508016175683001860529)
                ·
                  refine ⟨13852881012131762251395397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18470508016175683001860529 13852881012131762251395397)
                  ·
                    refine ⟨2597415189774705422136637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13852881012131762251395397 2597415189774705422136637)
                    ·
                      refine ⟨974030696165514533301239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597415189774705422136637 974030696165514533301239)
                      ·
                        rfl

theorem cell23_1896918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_1896918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896918 prefixEnd_1896918 := by exact prefixLift 1896918
  have htrace : WordTrace (prefixWord ++ tailWord_1896918) baseStart_1896918 baseEnd_1896918 := by
    simpa [prefixWord, tailWord_1896918, baseEnd_1896918] using wordTrace_append hprefix tailTrace_1896918
  have hstable : (prefixWord ++ tailWord_1896918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896918).length < 2 ^ (prefixWord ++ tailWord_1896918).sum := by decide
  have hdescent : baseEnd_1896918 < baseStart_1896918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896944 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_1896944 : Nat := 118140960795 + 1896944 * 2 ^ 59
def prefixEnd_1896944 : Nat := 4983230072969 + 3 ^ 40 * 1896944 * 2
def baseEnd_1896944 : Nat := 974044046662531431576119

theorem tailTrace_1896944 : CollatzResearch.WordTrace tailWord_1896944 prefixEnd_1896944 974044046662531431576119 := by
  unfold tailWord_1896944
  simp only [CollatzResearch.WordTrace]
  refine ⟨34593615819851667543780943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46124821093135556725041257 34593615819851667543780943)
  ·
    refine ⟨51890423729777501315671415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34593615819851667543780943 51890423729777501315671415)
    ·
      refine ⟨77835635594666251973507123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51890423729777501315671415 77835635594666251973507123)
      ·
        refine ⟨116753453391999377960260685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77835635594666251973507123 116753453391999377960260685)
        ·
          refine ⟨43782545021999766735097757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116753453391999377960260685 43782545021999766735097757)
          ·
            refine ⟨16418454383249912525661659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43782545021999766735097757 16418454383249912525661659)
            ·
              refine ⟨24627681574874868788492489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16418454383249912525661659 24627681574874868788492489)
              ·
                refine ⟨18470761181156151591369367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24627681574874868788492489 18470761181156151591369367)
                ·
                  refine ⟨27706141771734227387054051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18470761181156151591369367 27706141771734227387054051)
                  ·
                    refine ⟨41559212657601341080581077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27706141771734227387054051 41559212657601341080581077)
                    ·
                      refine ⟨974044046662531431576119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41559212657601341080581077 974044046662531431576119)
                      ·
                        rfl

theorem cell23_1896944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_1896944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896944 prefixEnd_1896944 := by exact prefixLift 1896944
  have htrace : WordTrace (prefixWord ++ tailWord_1896944) baseStart_1896944 baseEnd_1896944 := by
    simpa [prefixWord, tailWord_1896944, baseEnd_1896944] using wordTrace_append hprefix tailTrace_1896944
  have hstable : (prefixWord ++ tailWord_1896944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896944).length < 2 ^ (prefixWord ++ tailWord_1896944).sum := by decide
  have hdescent : baseEnd_1896944 < baseStart_1896944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896961 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_1896961 : Nat := 118140960795 + 1896961 * 2 ^ 59
def prefixEnd_1896961 : Nat := 4983230072969 + 3 ^ 40 * 1896961 * 2
def baseEnd_1896961 : Nat := 974052775833657865063541

theorem tailTrace_1896961 : CollatzResearch.WordTrace tailWord_1896961 prefixEnd_1896961 974052775833657865063541 := by
  unfold tailWord_1896961
  simp only [CollatzResearch.WordTrace]
  refine ⟨69187851680641746990930737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46125234453761164660620491 69187851680641746990930737)
  ·
    refine ⟨51890888760481310243198053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69187851680641746990930737 51890888760481310243198053)
    ·
      refine ⟨9729541642590245670599635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51890888760481310243198053 9729541642590245670599635)
      ·
        refine ⟨14594312463885368505899453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9729541642590245670599635 14594312463885368505899453)
        ·
          refine ⟨5472867173957013189712295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14594312463885368505899453 5472867173957013189712295)
          ·
            refine ⟨8209300760935519784568443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472867173957013189712295 8209300760935519784568443)
            ·
              refine ⟨12313951141403279676852665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209300760935519784568443 12313951141403279676852665)
              ·
                refine ⟨9235463356052459757639499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12313951141403279676852665 9235463356052459757639499)
                ·
                  refine ⟨13853195034078689636459249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235463356052459757639499 13853195034078689636459249)
                  ·
                    refine ⟨10389896275559017227344437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13853195034078689636459249 10389896275559017227344437)
                    ·
                      refine ⟨974052775833657865063541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10389896275559017227344437 974052775833657865063541)
                      ·
                        rfl

theorem cell23_1896961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_1896961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896961 prefixEnd_1896961 := by exact prefixLift 1896961
  have htrace : WordTrace (prefixWord ++ tailWord_1896961) baseStart_1896961 baseEnd_1896961 := by
    simpa [prefixWord, tailWord_1896961, baseEnd_1896961] using wordTrace_append hprefix tailTrace_1896961
  have hstable : (prefixWord ++ tailWord_1896961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896961).length < 2 ^ (prefixWord ++ tailWord_1896961).sum := by decide
  have hdescent : baseEnd_1896961 < baseStart_1896961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896966 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_1896966 : Nat := 118140960795 + 1896966 * 2 ^ 59
def prefixEnd_1896966 : Nat := 4983230072969 + 3 ^ 40 * 1896966 * 2
def baseEnd_1896966 : Nat := 974055343236930345501019

theorem tailTrace_1896966 : CollatzResearch.WordTrace tailWord_1896966 prefixEnd_1896966 974055343236930345501019 := by
  unfold tailWord_1896966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162126063925738526401961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46125356030415755229908501 2162126063925738526401961)
  ·
    refine ⟨1621594547944303894801471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2162126063925738526401961 1621594547944303894801471)
    ·
      refine ⟨2432391821916455842202207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621594547944303894801471 2432391821916455842202207)
      ·
        refine ⟨3648587732874683763303311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432391821916455842202207 3648587732874683763303311)
        ·
          refine ⟨5472881599312025644954967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3648587732874683763303311 5472881599312025644954967)
          ·
            refine ⟨8209322398968038467432451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5472881599312025644954967 8209322398968038467432451)
            ·
              refine ⟨12313983598452057701148677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209322398968038467432451 12313983598452057701148677)
              ·
                refine ⟨2308871924709760818965377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12313983598452057701148677 2308871924709760818965377)
                ·
                  refine ⟨1731653943532320614224033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2308871924709760818965377 1731653943532320614224033)
                  ·
                    refine ⟨1298740457649240460668025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1731653943532320614224033 1298740457649240460668025)
                    ·
                      refine ⟨974055343236930345501019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298740457649240460668025 974055343236930345501019)
                      ·
                        rfl

theorem cell23_1896966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_1896966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896966 prefixEnd_1896966 := by exact prefixLift 1896966
  have htrace : WordTrace (prefixWord ++ tailWord_1896966) baseStart_1896966 baseEnd_1896966 := by
    simpa [prefixWord, tailWord_1896966, baseEnd_1896966] using wordTrace_append hprefix tailTrace_1896966
  have hstable : (prefixWord ++ tailWord_1896966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896966).length < 2 ^ (prefixWord ++ tailWord_1896966).sum := by decide
  have hdescent : baseEnd_1896966 < baseStart_1896966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896988 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 6, 2]
def baseStart_1896988 : Nat := 118140960795 + 1896988 * 2 ^ 59
def prefixEnd_1896988 : Nat := 4983230072969 + 3 ^ 40 * 1896988 * 2
def baseEnd_1896988 : Nat := 974066639811329259425917

theorem tailTrace_1896988 : CollatzResearch.WordTrace tailWord_1896988 prefixEnd_1896988 974066639811329259425917 := by
  unfold tailWord_1896988
  simp only [CollatzResearch.WordTrace]
  refine ⟨34594418225771965301081809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46125890967695953734775745 34594418225771965301081809)
  ·
    refine ⟨25945813669328973975811357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34594418225771965301081809 25945813669328973975811357)
    ·
      refine ⟨9729680125998365240929259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25945813669328973975811357 9729680125998365240929259)
      ·
        refine ⟨14594520188997547861393889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9729680125998365240929259 14594520188997547861393889)
        ·
          refine ⟨10945890141748160896045417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14594520188997547861393889 10945890141748160896045417)
          ·
            refine ⟨8209417606311120672034063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10945890141748160896045417 8209417606311120672034063)
            ·
              refine ⟨12314126409466681008051095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209417606311120672034063 12314126409466681008051095)
              ·
                refine ⟨18471189614200021512076643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314126409466681008051095 18471189614200021512076643)
                ·
                  refine ⟨27706784421300032268114965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18471189614200021512076643 27706784421300032268114965)
                  ·
                    refine ⟨1298755519748439012567889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27706784421300032268114965 1298755519748439012567889)
                    ·
                      refine ⟨974066639811329259425917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298755519748439012567889 974066639811329259425917)
                      ·
                        rfl

theorem cell23_1896988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 6, 2].length) (baseStart_1896988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896988 prefixEnd_1896988 := by exact prefixLift 1896988
  have htrace : WordTrace (prefixWord ++ tailWord_1896988) baseStart_1896988 baseEnd_1896988 := by
    simpa [prefixWord, tailWord_1896988, baseEnd_1896988] using wordTrace_append hprefix tailTrace_1896988
  have hstable : (prefixWord ++ tailWord_1896988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896988).length < 2 ^ (prefixWord ++ tailWord_1896988).sum := by decide
  have hdescent : baseEnd_1896988 < baseStart_1896988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1896991 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1896991 : Nat := 118140960795 + 1896991 * 2 ^ 59
def prefixEnd_1896991 : Nat := 4983230072969 + 3 ^ 40 * 1896991 * 2
def baseEnd_1896991 : Nat := 974068180253292747688403

theorem tailTrace_1896991 : CollatzResearch.WordTrace tailWord_1896991 prefixEnd_1896991 974068180253292747688403 := by
  unfold tailWord_1896991
  simp only [CollatzResearch.WordTrace]
  refine ⟨69188945870533062114522827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46125963913688708076348551 69188945870533062114522827)
  ·
    refine ⟨103783418805799593171784241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69188945870533062114522827 103783418805799593171784241)
    ·
      refine ⟨77837564104349694878838181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103783418805799593171784241 77837564104349694878838181)
      ·
        refine ⟨14594543269565567789782159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77837564104349694878838181 14594543269565567789782159)
        ·
          refine ⟨21891814904348351684673239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14594543269565567789782159 21891814904348351684673239)
          ·
            refine ⟨32837722356522527527009859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21891814904348351684673239 32837722356522527527009859)
            ·
              refine ⟨49256583534783791290514789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32837722356522527527009859 49256583534783791290514789)
              ·
                refine ⟨9235609412771960866971523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49256583534783791290514789 9235609412771960866971523)
                ·
                  refine ⟨13853414119157941300457285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235609412771960866971523 13853414119157941300457285)
                  ·
                    refine ⟨2597515147342113993835741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13853414119157941300457285 2597515147342113993835741)
                    ·
                      refine ⟨974068180253292747688403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597515147342113993835741 974068180253292747688403)
                      ·
                        rfl

theorem cell23_1896991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1896991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1896991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1896991 prefixEnd_1896991 := by exact prefixLift 1896991
  have htrace : WordTrace (prefixWord ++ tailWord_1896991) baseStart_1896991 baseEnd_1896991 := by
    simpa [prefixWord, tailWord_1896991, baseEnd_1896991] using wordTrace_append hprefix tailTrace_1896991
  have hstable : (prefixWord ++ tailWord_1896991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1896991).length < 2 ^ (prefixWord ++ tailWord_1896991).sum := by decide
  have hdescent : baseEnd_1896991 < baseStart_1896991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1896991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897008 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3]
def baseStart_1897008 : Nat := 118140960795 + 1897008 * 2 ^ 59
def prefixEnd_1897008 : Nat := 4983230072969 + 3 ^ 40 * 1897008 * 2
def baseEnd_1897008 : Nat := 974076909424419181175825

theorem tailTrace_1897008 : CollatzResearch.WordTrace tailWord_1897008 prefixEnd_1897008 974076909424419181175825 := by
  unfold tailWord_1897008
  simp only [CollatzResearch.WordTrace]
  refine ⟨34594782955735737008945839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46126377274314316011927785 34594782955735737008945839)
  ·
    refine ⟨51892174433603605513418759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34594782955735737008945839 51892174433603605513418759)
    ·
      refine ⟨77838261650405408270128139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51892174433603605513418759 77838261650405408270128139)
      ·
        refine ⟨116757392475608112405192209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77838261650405408270128139 116757392475608112405192209)
        ·
          refine ⟨87568044356706084303894157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116757392475608112405192209 87568044356706084303894157)
          ·
            refine ⟨32838016633764781613960309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87568044356706084303894157 32838016633764781613960309)
            ·
              refine ⟨3078564059415448276308779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32838016633764781613960309 3078564059415448276308779)
              ·
                refine ⟨4617846089123172414463169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078564059415448276308779 4617846089123172414463169)
                ·
                  refine ⟨3463384566842379310847377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4617846089123172414463169 3463384566842379310847377)
                  ·
                    refine ⟨2597538425131784483135533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3463384566842379310847377 2597538425131784483135533)
                    ·
                      refine ⟨974076909424419181175825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597538425131784483135533 974076909424419181175825)
                      ·
                        rfl

theorem cell23_1897008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 3].length) (baseStart_1897008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897008 prefixEnd_1897008 := by exact prefixLift 1897008
  have htrace : WordTrace (prefixWord ++ tailWord_1897008) baseStart_1897008 baseEnd_1897008 := by
    simpa [prefixWord, tailWord_1897008, baseEnd_1897008] using wordTrace_append hprefix tailTrace_1897008
  have hstable : (prefixWord ++ tailWord_1897008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897008).length < 2 ^ (prefixWord ++ tailWord_1897008).sum := by decide
  have hdescent : baseEnd_1897008 < baseStart_1897008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897015 : List Nat := [1, 1, 3, 1, 2, 3, 4, 3, 1, 4]
def baseStart_1897015 : Nat := 118140960795 + 1897015 * 2 ^ 59
def prefixEnd_1897015 : Nat := 4983230072969 + 3 ^ 40 * 1897015 * 2
def baseEnd_1897015 : Nat := 324693501263000217929431

theorem tailTrace_1897015 : CollatzResearch.WordTrace tailWord_1897015 prefixEnd_1897015 324693501263000217929431 := by
  unfold tailWord_1897015
  simp only [CollatzResearch.WordTrace]
  refine ⟨69189821222446114213396499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46126547481630742808930999 69189821222446114213396499)
  ·
    refine ⟨103784731833669171320094749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69189821222446114213396499 103784731833669171320094749)
    ·
      refine ⟨38919274437625939245035531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103784731833669171320094749 38919274437625939245035531)
      ·
        refine ⟨58378911656438908867553297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38919274437625939245035531 58378911656438908867553297)
        ·
          refine ⟨43784183742329181650664973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58378911656438908867553297 43784183742329181650664973)
          ·
            refine ⟨16419068903373443118999365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43784183742329181650664973 16419068903373443118999365)
            ·
              refine ⟨3078575419382520584812381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16419068903373443118999365 3078575419382520584812381)
              ·
                refine ⟨1154465782268445219304643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3078575419382520584812381 1154465782268445219304643)
                ·
                  refine ⟨1731698673402667828956965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154465782268445219304643 1731698673402667828956965)
                  ·
                    refine ⟨324693501263000217929431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1731698673402667828956965 324693501263000217929431)
                    ·
                      rfl

theorem cell23_1897015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_1897015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897015 prefixEnd_1897015 := by exact prefixLift 1897015
  have htrace : WordTrace (prefixWord ++ tailWord_1897015) baseStart_1897015 baseEnd_1897015 := by
    simpa [prefixWord, tailWord_1897015, baseEnd_1897015] using wordTrace_append hprefix tailTrace_1897015
  have hstable : (prefixWord ++ tailWord_1897015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897015).length < 2 ^ (prefixWord ++ tailWord_1897015).sum := by decide
  have hdescent : baseEnd_1897015 < baseStart_1897015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897031 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1897031 : Nat := 118140960795 + 1897031 * 2 ^ 59
def prefixEnd_1897031 : Nat := 4983230072969 + 3 ^ 40 * 1897031 * 2
def baseEnd_1897031 : Nat := 974088719479472591188219

theorem tailTrace_1897031 : CollatzResearch.WordTrace tailWord_1897031 prefixEnd_1897031 974088719479472591188219 := by
  unfold tailWord_1897031
  simp only [CollatzResearch.WordTrace]
  refine ⟨69190404790388148945978947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46126936526925432630652631 69190404790388148945978947)
  ·
    refine ⟨103785607185582223418968421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69190404790388148945978947 103785607185582223418968421)
    ·
      refine ⟨19459801347296666891056579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103785607185582223418968421 19459801347296666891056579)
      ·
        refine ⟨29189702020945000336584869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19459801347296666891056579 29189702020945000336584869)
        ·
          refine ⟨5473069128927187563109663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29189702020945000336584869 5473069128927187563109663)
          ·
            refine ⟨8209603693390781344664495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473069128927187563109663 8209603693390781344664495)
            ·
              refine ⟨12314405540086172016996743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8209603693390781344664495 12314405540086172016996743)
              ·
                refine ⟨18471608310129258025495115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12314405540086172016996743 18471608310129258025495115)
                ·
                  refine ⟨27707412465193887038242673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18471608310129258025495115 27707412465193887038242673)
                  ·
                    refine ⟨20780559348895415278682005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27707412465193887038242673 20780559348895415278682005)
                    ·
                      refine ⟨974088719479472591188219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20780559348895415278682005 974088719479472591188219)
                      ·
                        rfl

theorem cell23_1897031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1897031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897031 prefixEnd_1897031 := by exact prefixLift 1897031
  have htrace : WordTrace (prefixWord ++ tailWord_1897031) baseStart_1897031 baseEnd_1897031 := by
    simpa [prefixWord, tailWord_1897031, baseEnd_1897031] using wordTrace_append hprefix tailTrace_1897031
  have hstable : (prefixWord ++ tailWord_1897031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897031).length < 2 ^ (prefixWord ++ tailWord_1897031).sum := by decide
  have hdescent : baseEnd_1897031 < baseStart_1897031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897048 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 1, 5, 2]
def baseStart_1897048 : Nat := 118140960795 + 1897048 * 2 ^ 59
def prefixEnd_1897048 : Nat := 4983230072969 + 3 ^ 40 * 1897048 * 2
def baseEnd_1897048 : Nat := 974097448650599024675641

theorem tailTrace_1897048 : CollatzResearch.WordTrace tailWord_1897048 prefixEnd_1897048 974097448650599024675641 := by
  unfold tailWord_1897048
  simp only [CollatzResearch.WordTrace]
  refine ⟨34595512415663280424673899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46127349887551040566231865 34595512415663280424673899)
  ·
    refine ⟨51893268623494920637010849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34595512415663280424673899 51893268623494920637010849)
    ·
      refine ⟨38919951467621190477758137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51893268623494920637010849 38919951467621190477758137)
      ·
        refine ⟨29189963600715892858318603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38919951467621190477758137 29189963600715892858318603)
        ·
          refine ⟨43784945401073839287477905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29189963600715892858318603 43784945401073839287477905)
          ·
            refine ⟨32838709050805379465608429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43784945401073839287477905 32838709050805379465608429)
            ·
              refine ⟨12314515894052017299603161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32838709050805379465608429 12314515894052017299603161)
              ·
                refine ⟨9235886920539012974702371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12314515894052017299603161 9235886920539012974702371)
                ·
                  refine ⟨13853830380808519462053557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9235886920539012974702371 13853830380808519462053557)
                  ·
                    refine ⟨1298796598200798699567521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13853830380808519462053557 1298796598200798699567521)
                    ·
                      refine ⟨974097448650599024675641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298796598200798699567521 974097448650599024675641)
                      ·
                        rfl

theorem cell23_1897048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_1897048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897048 prefixEnd_1897048 := by exact prefixLift 1897048
  have htrace : WordTrace (prefixWord ++ tailWord_1897048) baseStart_1897048 baseEnd_1897048 := by
    simpa [prefixWord, tailWord_1897048, baseEnd_1897048] using wordTrace_append hprefix tailTrace_1897048
  have hstable : (prefixWord ++ tailWord_1897048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897048).length < 2 ^ (prefixWord ++ tailWord_1897048).sum := by decide
  have hdescent : baseEnd_1897048 < baseStart_1897048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897071 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 1, 6]
def baseStart_1897071 : Nat := 118140960795 + 1897071 * 2 ^ 59
def prefixEnd_1897071 : Nat := 4983230072969 + 3 ^ 40 * 1897071 * 2
def baseEnd_1897071 : Nat := 324703086235217478229345

theorem tailTrace_1897071 : CollatzResearch.WordTrace tailWord_1897071 prefixEnd_1897071 324703086235217478229345 := by
  unfold tailWord_1897071
  simp only [CollatzResearch.WordTrace]
  refine ⟨69191863710243235777435067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46127909140162157184956711 69191863710243235777435067)
  ·
    refine ⟨103787795565364853666152601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69191863710243235777435067 103787795565364853666152601)
    ·
      refine ⟨77840846674023640249614451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103787795565364853666152601 77840846674023640249614451)
      ·
        refine ⟨116761270011035460374421677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77840846674023640249614451 116761270011035460374421677)
        ·
          refine ⟨43785476254138297640408129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116761270011035460374421677 43785476254138297640408129)
          ·
            refine ⟨32839107190603723230306097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43785476254138297640408129 32839107190603723230306097)
            ·
              refine ⟨24629330392952792422729573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32839107190603723230306097 24629330392952792422729573)
              ·
                refine ⟨4617999448678648579261795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24629330392952792422729573 4617999448678648579261795)
                ·
                  refine ⟨6926999173017972868892693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4617999448678648579261795 6926999173017972868892693)
                  ·
                    refine ⟨324703086235217478229345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6926999173017972868892693 324703086235217478229345)
                    ·
                      rfl

theorem cell23_1897071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_1897071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897071 prefixEnd_1897071 := by exact prefixLift 1897071
  have htrace : WordTrace (prefixWord ++ tailWord_1897071) baseStart_1897071 baseEnd_1897071 := by
    simpa [prefixWord, tailWord_1897071, baseEnd_1897071] using wordTrace_append hprefix tailTrace_1897071
  have hstable : (prefixWord ++ tailWord_1897071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897071).length < 2 ^ (prefixWord ++ tailWord_1897071).sum := by decide
  have hdescent : baseEnd_1897071 < baseStart_1897071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897088 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 4, 4]
def baseStart_1897088 : Nat := 118140960795 + 1897088 * 2 ^ 59
def prefixEnd_1897088 : Nat := 4983230072969 + 3 ^ 40 * 1897088 * 2
def baseEnd_1897088 : Nat := 324705995958926289391819

theorem tailTrace_1897088 : CollatzResearch.WordTrace tailWord_1897088 prefixEnd_1897088 324705995958926289391819 := by
  unfold tailWord_1897088
  simp only [CollatzResearch.WordTrace]
  refine ⟨34596241875590823840401959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46128322500787765120535945 34596241875590823840401959)
  ·
    refine ⟨51894362813386235760602939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34596241875590823840401959 51894362813386235760602939)
    ·
      refine ⟨77841544220079353640904409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51894362813386235760602939 77841544220079353640904409)
      ·
        refine ⟨58381158165059515230678307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77841544220079353640904409 58381158165059515230678307)
        ·
          refine ⟨87571737247589272846017461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58381158165059515230678307 87571737247589272846017461)
          ·
            refine ⟨8209850366961494329314137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 87571737247589272846017461 8209850366961494329314137)
            ·
              refine ⟨6157387775221120746985603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8209850366961494329314137 6157387775221120746985603)
              ·
                refine ⟨9236081662831681120478405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6157387775221120746985603 9236081662831681120478405)
                ·
                  refine ⟨1731765311780940210089701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9236081662831681120478405 1731765311780940210089701)
                  ·
                    refine ⟨324705995958926289391819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1731765311780940210089701 324705995958926289391819)
                    ·
                      rfl

theorem cell23_1897088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 4, 4].length) (baseStart_1897088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897088 prefixEnd_1897088 := by exact prefixLift 1897088
  have htrace : WordTrace (prefixWord ++ tailWord_1897088) baseStart_1897088 baseEnd_1897088 := by
    simpa [prefixWord, tailWord_1897088, baseEnd_1897088] using wordTrace_append hprefix tailTrace_1897088
  have hstable : (prefixWord ++ tailWord_1897088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897088).length < 2 ^ (prefixWord ++ tailWord_1897088).sum := by decide
  have hdescent : baseEnd_1897088 < baseStart_1897088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897089 : List Nat := [1, 2, 4, 2, 1, 1, 5, 2, 1, 1, 3]
def baseStart_1897089 : Nat := 118140960795 + 1897089 * 2 ^ 59
def prefixEnd_1897089 : Nat := 4983230072969 + 3 ^ 40 * 1897089 * 2
def baseEnd_1897089 : Nat := 974118501357433364262953

theorem tailTrace_1897089 : CollatzResearch.WordTrace tailWord_1897089 prefixEnd_1897089 974118501357433364262953 := by
  unfold tailWord_1897089
  simp only [CollatzResearch.WordTrace]
  refine ⟨69192520224178024851590321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46128346816118683234393547 69192520224178024851590321)
  ·
    refine ⟨51894390168133518638692741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69192520224178024851590321 51894390168133518638692741)
    ·
      refine ⟨9730198156525034744754889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51894390168133518638692741 9730198156525034744754889)
      ·
        refine ⟨7297648617393776058566167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9730198156525034744754889 7297648617393776058566167)
        ·
          refine ⟨10946472926090664087849251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297648617393776058566167 10946472926090664087849251)
          ·
            refine ⟨16419709389135996131773877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946472926090664087849251 16419709389135996131773877)
            ·
              refine ⟨1539347755231499637353801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16419709389135996131773877 1539347755231499637353801)
              ·
                refine ⟨1154510816423624728015351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1539347755231499637353801 1154510816423624728015351)
                ·
                  refine ⟨1731766224635437092023027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154510816423624728015351 1731766224635437092023027)
                  ·
                    refine ⟨2597649336953155638034541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1731766224635437092023027 2597649336953155638034541)
                    ·
                      refine ⟨974118501357433364262953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597649336953155638034541 974118501357433364262953)
                      ·
                        rfl

theorem cell23_1897089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_1897089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897089 prefixEnd_1897089 := by exact prefixLift 1897089
  have htrace : WordTrace (prefixWord ++ tailWord_1897089) baseStart_1897089 baseEnd_1897089 := by
    simpa [prefixWord, tailWord_1897089, baseEnd_1897089] using wordTrace_append hprefix tailTrace_1897089
  have hstable : (prefixWord ++ tailWord_1897089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897089).length < 2 ^ (prefixWord ++ tailWord_1897089).sum := by decide
  have hdescent : baseEnd_1897089 < baseStart_1897089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897091 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6]
def baseStart_1897091 : Nat := 118140960795 + 1897091 * 2 ^ 59
def prefixEnd_1897091 : Nat := 4983230072969 + 3 ^ 40 * 1897091 * 2
def baseEnd_1897091 : Nat := 974119528318742356437943

theorem tailTrace_1897091 : CollatzResearch.WordTrace tailWord_1897091 prefixEnd_1897091 974119528318742356437943 := by
  unfold tailWord_1897091
  simp only [CollatzResearch.WordTrace]
  refine ⟨69192593170170779193163127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46128395446780519462108751 69192593170170779193163127)
  ·
    refine ⟨103788889755256168789744691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69192593170170779193163127 103788889755256168789744691)
    ·
      refine ⟨155683334632884253184617037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103788889755256168789744691 155683334632884253184617037)
      ·
        refine ⟨58381250487331594944231389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 155683334632884253184617037 58381250487331594944231389)
        ·
          refine ⟨21892968932749348104086771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58381250487331594944231389 21892968932749348104086771)
          ·
            refine ⟨32839453399124022156130157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21892968932749348104086771 32839453399124022156130157)
            ·
              refine ⟨12314795024671508308548809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32839453399124022156130157 12314795024671508308548809)
              ·
                refine ⟨9236096268503631231411607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12314795024671508308548809 9236096268503631231411607)
                ·
                  refine ⟨13854144402755446847117411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9236096268503631231411607 13854144402755446847117411)
                  ·
                    refine ⟨20781216604133170270676117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13854144402755446847117411 20781216604133170270676117)
                    ·
                      refine ⟨974119528318742356437943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20781216604133170270676117 974119528318742356437943)
                      ·
                        rfl

theorem cell23_1897091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 6].length) (baseStart_1897091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897091 prefixEnd_1897091 := by exact prefixLift 1897091
  have htrace : WordTrace (prefixWord ++ tailWord_1897091) baseStart_1897091 baseEnd_1897091 := by
    simpa [prefixWord, tailWord_1897091, baseEnd_1897091] using wordTrace_append hprefix tailTrace_1897091
  have hstable : (prefixWord ++ tailWord_1897091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897091).length < 2 ^ (prefixWord ++ tailWord_1897091).sum := by decide
  have hdescent : baseEnd_1897091 < baseStart_1897091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897118 : List Nat := [4, 3, 1, 1, 1, 1, 1, 11]
def baseStart_1897118 : Nat := 118140960795 + 1897118 * 2 ^ 59
def prefixEnd_1897118 : Nat := 4983230072969 + 3 ^ 40 * 1897118 * 2
def baseEnd_1897118 : Nat := 36079014529496805585197

theorem tailTrace_1897118 : CollatzResearch.WordTrace tailWord_1897118 prefixEnd_1897118 36079014529496805585197 := by
  unfold tailWord_1897118
  simp only [CollatzResearch.WordTrace]
  refine ⟨8649197242634120350549501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46129051960715308536264005 8649197242634120350549501)
  ·
    refine ⟨3243448965987795131456063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8649197242634120350549501 3243448965987795131456063)
    ·
      refine ⟨4865173448981692697184095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3243448965987795131456063 4865173448981692697184095)
      ·
        refine ⟨7297760173472539045776143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4865173448981692697184095 7297760173472539045776143)
        ·
          refine ⟨10946640260208808568664215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7297760173472539045776143 10946640260208808568664215)
          ·
            refine ⟨16419960390313212852996323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10946640260208808568664215 16419960390313212852996323)
            ·
              refine ⟨24629940585469819279494485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16419960390313212852996323 24629940585469819279494485)
              ·
                refine ⟨36079014529496805585197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 24629940585469819279494485 36079014529496805585197)
                ·
                  rfl

theorem cell23_1897118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_1897118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897118 prefixEnd_1897118 := by exact prefixLift 1897118
  have htrace : WordTrace (prefixWord ++ tailWord_1897118) baseStart_1897118 baseEnd_1897118 := by
    simpa [prefixWord, tailWord_1897118, baseEnd_1897118] using wordTrace_append hprefix tailTrace_1897118
  have hstable : (prefixWord ++ tailWord_1897118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897118).length < 2 ^ (prefixWord ++ tailWord_1897118).sum := by decide
  have hdescent : baseEnd_1897118 < baseStart_1897118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897162 : List Nat := [3, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_1897162 : Nat := 118140960795 + 1897162 * 2 ^ 59
def prefixEnd_1897162 : Nat := 4983230072969 + 3 ^ 40 * 1897162 * 2
def baseEnd_1897162 : Nat := 974155985445211578650117

theorem tailTrace_1897162 : CollatzResearch.WordTrace tailWord_1897162 prefixEnd_1897162 974155985445211578650117 := by
  unfold tailWord_1897162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17298795688228389579749435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46130121835275705545998493 17298795688228389579749435)
  ·
    refine ⟨25948193532342584369624153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17298795688228389579749435 25948193532342584369624153)
    ·
      refine ⟨19461145149256938277218115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25948193532342584369624153 19461145149256938277218115)
      ·
        refine ⟨29191717723885407415827173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19461145149256938277218115 29191717723885407415827173)
        ·
          refine ⟨5473447073228513890467595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29191717723885407415827173 5473447073228513890467595)
          ·
            refine ⟨8210170609842770835701393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473447073228513890467595 8210170609842770835701393)
            ·
              refine ⟨6157627957382078126776045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8210170609842770835701393 6157627957382078126776045)
              ·
                refine ⟨2309110484018279297541017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6157627957382078126776045 2309110484018279297541017)
                ·
                  refine ⟨1731832863013709473155763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309110484018279297541017 1731832863013709473155763)
                  ·
                    refine ⟨2597749294520564209733645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1731832863013709473155763 2597749294520564209733645)
                    ·
                      refine ⟨974155985445211578650117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597749294520564209733645 974155985445211578650117)
                      ·
                        rfl

theorem cell23_1897162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_1897162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897162 prefixEnd_1897162 := by exact prefixLift 1897162
  have htrace : WordTrace (prefixWord ++ tailWord_1897162) baseStart_1897162 baseEnd_1897162 := by
    simpa [prefixWord, tailWord_1897162, baseEnd_1897162] using wordTrace_append hprefix tailTrace_1897162
  have hstable : (prefixWord ++ tailWord_1897162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897162).length < 2 ^ (prefixWord ++ tailWord_1897162).sum := by decide
  have hdescent : baseEnd_1897162 < baseStart_1897162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897189 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 1, 3, 2]
def baseStart_1897189 : Nat := 118140960795 + 1897189 * 2 ^ 59
def prefixEnd_1897189 : Nat := 4983230072969 + 3 ^ 40 * 1897189 * 2
def baseEnd_1897189 : Nat := 974169849422882973012493

theorem tailTrace_1897189 : CollatzResearch.WordTrace tailWord_1897189 prefixEnd_1897189 974169849422882973012493 := by
  unfold tailWord_1897189
  simp only [CollatzResearch.WordTrace]
  refine ⟨69196167523815741930230621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46130778349210494620153747 69196167523815741930230621)
  ·
    refine ⟨25948562821430903223836483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69196167523815741930230621 25948562821430903223836483)
    ·
      refine ⟨38922844232146354835754725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25948562821430903223836483 38922844232146354835754725)
      ·
        refine ⟨7298033293527441531704011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38922844232146354835754725 7298033293527441531704011)
        ·
          refine ⟨10947049940291162297556017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7298033293527441531704011 10947049940291162297556017)
          ·
            refine ⟨8210287455218371723167013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10947049940291162297556017 8210287455218371723167013)
            ·
              refine ⟨1539428897853444698093815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8210287455218371723167013 1539428897853444698093815)
              ·
                refine ⟨2309143346780167047140723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539428897853444698093815 2309143346780167047140723)
                ·
                  refine ⟨3463715020170250570711085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309143346780167047140723 3463715020170250570711085)
                  ·
                    refine ⟨1298893132563843964016657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3463715020170250570711085 1298893132563843964016657)
                    ·
                      refine ⟨974169849422882973012493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298893132563843964016657 974169849422882973012493)
                      ·
                        rfl

theorem cell23_1897189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_1897189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897189 prefixEnd_1897189 := by exact prefixLift 1897189
  have htrace : WordTrace (prefixWord ++ tailWord_1897189) baseStart_1897189 baseEnd_1897189 := by
    simpa [prefixWord, tailWord_1897189, baseEnd_1897189] using wordTrace_append hprefix tailTrace_1897189
  have hstable : (prefixWord ++ tailWord_1897189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897189).length < 2 ^ (prefixWord ++ tailWord_1897189).sum := by decide
  have hdescent : baseEnd_1897189 < baseStart_1897189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897208 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 7]
def baseStart_1897208 : Nat := 118140960795 + 1897208 * 2 ^ 59
def prefixEnd_1897208 : Nat := 4983230072969 + 3 ^ 40 * 1897208 * 2
def baseEnd_1897208 : Nat := 108242178395035377630545

theorem tailTrace_1897208 : CollatzResearch.WordTrace tailWord_1897208 prefixEnd_1897208 108242178395035377630545 := by
  unfold tailWord_1897208
  simp only [CollatzResearch.WordTrace]
  refine ⟨34598430255373454087586139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46131240340497938783448185 34598430255373454087586139)
  ·
    refine ⟨51897645383060181131379209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34598430255373454087586139 51897645383060181131379209)
    ·
      refine ⟨38923234037295135848534407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51897645383060181131379209 38923234037295135848534407)
      ·
        refine ⟨58384851055942703772801611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38923234037295135848534407 58384851055942703772801611)
        ·
          refine ⟨87577276583914055659202417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58384851055942703772801611 87577276583914055659202417)
          ·
            refine ⟨65682957437935541744401813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87577276583914055659202417 65682957437935541744401813)
            ·
              refine ⟨3078888629903228519268835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65682957437935541744401813 3078888629903228519268835)
              ·
                refine ⟨4618332944854842778903253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3078888629903228519268835 4618332944854842778903253)
                ·
                  refine ⟨108242178395035377630545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4618332944854842778903253 108242178395035377630545)
                  ·
                    rfl

theorem cell23_1897208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 7].length) (baseStart_1897208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897208 prefixEnd_1897208 := by exact prefixLift 1897208
  have htrace : WordTrace (prefixWord ++ tailWord_1897208) baseStart_1897208 baseEnd_1897208 := by
    simpa [prefixWord, tailWord_1897208, baseEnd_1897208] using wordTrace_append hprefix tailTrace_1897208
  have hstable : (prefixWord ++ tailWord_1897208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897208).length < 2 ^ (prefixWord ++ tailWord_1897208).sum := by decide
  have hdescent : baseEnd_1897208 < baseStart_1897208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897270 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_1897270 : Nat := 118140960795 + 1897270 * 2 ^ 59
def prefixEnd_1897270 : Nat := 4983230072969 + 3 ^ 40 * 1897270 * 2
def baseEnd_1897270 : Nat := 974211441355897156099621

theorem tailTrace_1897270 : CollatzResearch.WordTrace tailWord_1897270 prefixEnd_1897270 974211441355897156099621 := by
  unfold tailWord_1897270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324945114782643297745579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46132747891014861842619509 4324945114782643297745579)
  ·
    refine ⟨6487417672173964946618369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4324945114782643297745579 6487417672173964946618369)
    ·
      refine ⟨4865563254130473709963777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6487417672173964946618369 4865563254130473709963777)
      ·
        refine ⟨3649172440597855282472833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4865563254130473709963777 3649172440597855282472833)
        ·
          refine ⟨2736879330448391461854625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3649172440597855282472833 2736879330448391461854625)
          ·
            refine ⟨2052659497836293596390969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2736879330448391461854625 2052659497836293596390969)
            ·
              refine ⟨1539494623377220197293227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2052659497836293596390969 1539494623377220197293227)
              ·
                refine ⟨2309241935065830295939841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1539494623377220197293227 2309241935065830295939841)
                ·
                  refine ⟨1731931451299372721954881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2309241935065830295939841 1731931451299372721954881)
                  ·
                    refine ⟨1298948588474529541466161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1731931451299372721954881 1298948588474529541466161)
                    ·
                      refine ⟨974211441355897156099621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1298948588474529541466161 974211441355897156099621)
                      ·
                        rfl

theorem cell23_1897270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_1897270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897270 prefixEnd_1897270 := by exact prefixLift 1897270
  have htrace : WordTrace (prefixWord ++ tailWord_1897270) baseStart_1897270 baseEnd_1897270 := by
    simpa [prefixWord, tailWord_1897270, baseEnd_1897270] using wordTrace_append hprefix tailTrace_1897270
  have hstable : (prefixWord ++ tailWord_1897270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897270).length < 2 ^ (prefixWord ++ tailWord_1897270).sum := by decide
  have hdescent : baseEnd_1897270 < baseStart_1897270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897292 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1897292 : Nat := 118140960795 + 1897292 * 2 ^ 59
def prefixEnd_1897292 : Nat := 4983230072969 + 3 ^ 40 * 1897292 * 2
def baseEnd_1897292 : Nat := 974222737930296070024519

theorem tailTrace_1897292 : CollatzResearch.WordTrace tailWord_1897292 prefixEnd_1897292 974222737930296070024519 := by
  unfold tailWord_1897292
  simp only [CollatzResearch.WordTrace]
  refine ⟨34599962121221295260615065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46133282828295060347486753 34599962121221295260615065)
  ·
    refine ⟨25949971590915971445461299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34599962121221295260615065 25949971590915971445461299)
    ·
      refine ⟨38924957386373957168191949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25949971590915971445461299 38924957386373957168191949)
      ·
        refine ⟨14596859019890233938071981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38924957386373957168191949 14596859019890233938071981)
        ·
          refine ⟨5473822132458837726776993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14596859019890233938071981 5473822132458837726776993)
          ·
            refine ⟨4105366599344128295082745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5473822132458837726776993 4105366599344128295082745)
            ·
              refine ⟨3079024949508096221312059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105366599344128295082745 3079024949508096221312059)
              ·
                refine ⟨4618537424262144331968089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079024949508096221312059 4618537424262144331968089)
                ·
                  refine ⟨3463903068196608248976067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4618537424262144331968089 3463903068196608248976067)
                  ·
                    refine ⟨5195854602294912373464101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3463903068196608248976067 5195854602294912373464101)
                    ·
                      refine ⟨974222737930296070024519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5195854602294912373464101 974222737930296070024519)
                      ·
                        rfl

theorem cell23_1897292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1897292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897292 prefixEnd_1897292 := by exact prefixLift 1897292
  have htrace : WordTrace (prefixWord ++ tailWord_1897292) baseStart_1897292 baseEnd_1897292 := by
    simpa [prefixWord, tailWord_1897292, baseEnd_1897292] using wordTrace_append hprefix tailTrace_1897292
  have hstable : (prefixWord ++ tailWord_1897292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897292).length < 2 ^ (prefixWord ++ tailWord_1897292).sum := by decide
  have hdescent : baseEnd_1897292 < baseStart_1897292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897315 : List Nat := [1, 1, 1, 5, 3, 1, 1, 4, 6]
def baseStart_1897315 : Nat := 118140960795 + 1897315 * 2 ^ 59
def prefixEnd_1897315 : Nat := 4983230072969 + 3 ^ 40 * 1897315 * 2
def baseEnd_1897315 : Nat := 108248283109483275559657

theorem tailTrace_1897315 : CollatzResearch.WordTrace tailWord_1897315 prefixEnd_1897315 108248283109483275559657 := by
  unfold tailWord_1897315
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200763121359265449317399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46133842080906176966211599 69200763121359265449317399)
  ·
    refine ⟨103801144682038898173976099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69200763121359265449317399 103801144682038898173976099)
    ·
      refine ⟨155701717023058347260964149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103801144682038898173976099 155701717023058347260964149)
      ·
        refine ⟨14597035970911720055715389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 155701717023058347260964149 14597035970911720055715389)
        ·
          refine ⟨5473888489091895020893271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14597035970911720055715389 5473888489091895020893271)
          ·
            refine ⟨8210832733637842531339907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5473888489091895020893271 8210832733637842531339907)
            ·
              refine ⟨12316249100456763797009861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8210832733637842531339907 12316249100456763797009861)
              ·
                refine ⟨2309296706335643211939349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12316249100456763797009861 2309296706335643211939349)
                ·
                  refine ⟨108248283109483275559657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2309296706335643211939349 108248283109483275559657)
                  ·
                    rfl

theorem cell23_1897315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 6].length) (baseStart_1897315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897315 prefixEnd_1897315 := by exact prefixLift 1897315
  have htrace : WordTrace (prefixWord ++ tailWord_1897315) baseStart_1897315 baseEnd_1897315 := by
    simpa [prefixWord, tailWord_1897315, baseEnd_1897315] using wordTrace_append hprefix tailTrace_1897315
  have hstable : (prefixWord ++ tailWord_1897315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897315).length < 2 ^ (prefixWord ++ tailWord_1897315).sum := by decide
  have hdescent : baseEnd_1897315 < baseStart_1897315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897319 : List Nat := [1, 1, 5, 1, 2, 3, 1, 4, 1, 4]
def baseStart_1897319 : Nat := 118140960795 + 1897319 * 2 ^ 59
def prefixEnd_1897319 : Nat := 4983230072969 + 3 ^ 40 * 1897319 * 2
def baseEnd_1897319 : Nat := 324745533969322488128965

theorem tailTrace_1897319 : CollatzResearch.WordTrace tailWord_1897319 prefixEnd_1897319 324745533969322488128965 := by
  unfold tailWord_1897319
  simp only [CollatzResearch.WordTrace]
  refine ⟨69200909013344774132463011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46133939342229849421642007 69200909013344774132463011)
  ·
    refine ⟨103801363520017161198694517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69200909013344774132463011 103801363520017161198694517)
    ·
      refine ⟨9731377830001608862377611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103801363520017161198694517 9731377830001608862377611)
      ·
        refine ⟨14597066745002413293566417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731377830001608862377611 14597066745002413293566417)
        ·
          refine ⟨10947800058751809970174813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14597066745002413293566417 10947800058751809970174813)
          ·
            refine ⟨4105425022031928738815555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10947800058751809970174813 4105425022031928738815555)
            ·
              refine ⟨6158137533047893108223333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105425022031928738815555 6158137533047893108223333)
              ·
                refine ⟨1154650787446479957791875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6158137533047893108223333 1154650787446479957791875)
                ·
                  refine ⟨1731976181169719936687813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1154650787446479957791875 1731976181169719936687813)
                  ·
                    refine ⟨324745533969322488128965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1731976181169719936687813 324745533969322488128965)
                    ·
                      rfl

theorem cell23_1897319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_1897319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897319 prefixEnd_1897319 := by exact prefixLift 1897319
  have htrace : WordTrace (prefixWord ++ tailWord_1897319) baseStart_1897319 baseEnd_1897319 := by
    simpa [prefixWord, tailWord_1897319, baseEnd_1897319] using wordTrace_append hprefix tailTrace_1897319
  have hstable : (prefixWord ++ tailWord_1897319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897319).length < 2 ^ (prefixWord ++ tailWord_1897319).sum := by decide
  have hdescent : baseEnd_1897319 < baseStart_1897319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897325 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_1897325 : Nat := 118140960795 + 1897325 * 2 ^ 59
def prefixEnd_1897325 : Nat := 4983230072969 + 3 ^ 40 * 1897325 * 2
def baseEnd_1897325 : Nat := 974239682791894440911867

theorem tailTrace_1897325 : CollatzResearch.WordTrace tailWord_1897325 prefixEnd_1897325 974239682791894440911867 := by
  unfold tailWord_1897325
  simp only [CollatzResearch.WordTrace]
  refine ⟨69201127851323037157181429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46134085234215358104787619 69201127851323037157181429)
  ·
    refine ⟨6487605736061534733485759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69201127851323037157181429 6487605736061534733485759)
    ·
      refine ⟨9731408604092302100228639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6487605736061534733485759 9731408604092302100228639)
      ·
        refine ⟨14597112906138453150342959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9731408604092302100228639 14597112906138453150342959)
        ·
          refine ⟨21895669359207679725514439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14597112906138453150342959 21895669359207679725514439)
          ·
            refine ⟨32843504038811519588271659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21895669359207679725514439 32843504038811519588271659)
            ·
              refine ⟨49265256058217279382407489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32843504038811519588271659 49265256058217279382407489)
              ·
                refine ⟨36948942043662959536805617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49265256058217279382407489 36948942043662959536805617)
                ·
                  refine ⟨27711706532747219652604213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36948942043662959536805617 27711706532747219652604213)
                  ·
                    refine ⟨2597972487445051842431645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27711706532747219652604213 2597972487445051842431645)
                    ·
                      refine ⟨974239682791894440911867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2597972487445051842431645 974239682791894440911867)
                      ·
                        rfl

theorem cell23_1897325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_1897325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897325 prefixEnd_1897325 := by exact prefixLift 1897325
  have htrace : WordTrace (prefixWord ++ tailWord_1897325) baseStart_1897325 baseEnd_1897325 := by
    simpa [prefixWord, tailWord_1897325, baseEnd_1897325] using wordTrace_append hprefix tailTrace_1897325
  have hstable : (prefixWord ++ tailWord_1897325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897325).length < 2 ^ (prefixWord ++ tailWord_1897325).sum := by decide
  have hdescent : baseEnd_1897325 < baseStart_1897325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897338 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1897338 : Nat := 118140960795 + 1897338 * 2 ^ 59
def prefixEnd_1897338 : Nat := 4983230072969 + 3 ^ 40 * 1897338 * 2
def baseEnd_1897338 : Nat := 974246358040402890049307

theorem tailTrace_1897338 : CollatzResearch.WordTrace tailWord_1897338 prefixEnd_1897338 974246358040402890049307 := by
  unfold tailWord_1897338
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300400500068985094351167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46134401333517293584936445 17300400500068985094351167)
  ·
    refine ⟨25950600750103477641526751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17300400500068985094351167 25950600750103477641526751)
    ·
      refine ⟨38925901125155216462290127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25950600750103477641526751 38925901125155216462290127)
      ·
        refine ⟨58388851687732824693435191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38925901125155216462290127 58388851687732824693435191)
        ·
          refine ⟨87583277531599237040152787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58388851687732824693435191 87583277531599237040152787)
          ·
            refine ⟨131374916297398855560229181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87583277531599237040152787 131374916297398855560229181)
            ·
              refine ⟨49265593611524570835085943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131374916297398855560229181 49265593611524570835085943)
              ·
                refine ⟨73898390417286856252628915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49265593611524570835085943 73898390417286856252628915)
                ·
                  refine ⟨110847585625930284378943373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73898390417286856252628915 110847585625930284378943373)
                  ·
                    refine ⟨41567844609723856642103765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 110847585625930284378943373 41567844609723856642103765)
                    ·
                      refine ⟨974246358040402890049307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41567844609723856642103765 974246358040402890049307)
                      ·
                        rfl

theorem cell23_1897338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1897338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897338 prefixEnd_1897338 := by exact prefixLift 1897338
  have htrace : WordTrace (prefixWord ++ tailWord_1897338) baseStart_1897338 baseEnd_1897338 := by
    simpa [prefixWord, tailWord_1897338, baseEnd_1897338] using wordTrace_append hprefix tailTrace_1897338
  have hstable : (prefixWord ++ tailWord_1897338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897338).length < 2 ^ (prefixWord ++ tailWord_1897338).sum := by decide
  have hdescent : baseEnd_1897338 < baseStart_1897338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897346 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1897346 : Nat := 118140960795 + 1897346 * 2 ^ 59
def prefixEnd_1897346 : Nat := 4983230072969 + 3 ^ 40 * 1897346 * 2
def baseEnd_1897346 : Nat := 974250465885638858749271

theorem tailTrace_1897346 : CollatzResearch.WordTrace tailWord_1897346 prefixEnd_1897346 974250465885638858749271 := by
  unfold tailWord_1897346
  simp only [CollatzResearch.WordTrace]
  refine ⟨17300473446061739435923973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46134595856164638495797261 17300473446061739435923973)
  ·
    refine ⟨3243838771136576144235745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17300473446061739435923973 3243838771136576144235745)
    ·
      refine ⟨2432879078352432108176809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243838771136576144235745 2432879078352432108176809)
      ·
        refine ⟨1824659308764324081132607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2432879078352432108176809 1824659308764324081132607)
        ·
          refine ⟨2736988963146486121698911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1824659308764324081132607 2736988963146486121698911)
          ·
            refine ⟨4105483444719729182548367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2736988963146486121698911 4105483444719729182548367)
            ·
              refine ⟨6158225167079593773822551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4105483444719729182548367 6158225167079593773822551)
              ·
                refine ⟨9237337750619390660733827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6158225167079593773822551 9237337750619390660733827)
                ·
                  refine ⟨13856006625929085991100741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9237337750619390660733827 13856006625929085991100741)
                  ·
                    refine ⟨2598001242361703623331389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13856006625929085991100741 2598001242361703623331389)
                    ·
                      refine ⟨974250465885638858749271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2598001242361703623331389 974250465885638858749271)
                      ·
                        rfl

theorem cell23_1897346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1897346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897346 prefixEnd_1897346 := by exact prefixLift 1897346
  have htrace : WordTrace (prefixWord ++ tailWord_1897346) baseStart_1897346 baseEnd_1897346 := by
    simpa [prefixWord, tailWord_1897346, baseEnd_1897346] using wordTrace_append hprefix tailTrace_1897346
  have hstable : (prefixWord ++ tailWord_1897346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897346).length < 2 ^ (prefixWord ++ tailWord_1897346).sum := by decide
  have hdescent : baseEnd_1897346 < baseStart_1897346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897366 : List Nat := [5, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1897366 : Nat := 118140960795 + 1897366 * 2 ^ 59
def prefixEnd_1897366 : Nat := 4983230072969 + 3 ^ 40 * 1897366 * 2
def baseEnd_1897366 : Nat := 108251192833192086722131

theorem tailTrace_1897366 : CollatzResearch.WordTrace tailWord_1897366 prefixEnd_1897366 108251192833192086722131 := by
  unfold tailWord_1897366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325163952760906322463997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46135082162783000772949301 4325163952760906322463997)
  ·
    refine ⟨1621936482285339870923999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4325163952760906322463997 1621936482285339870923999)
    ·
      refine ⟨2432904723428009806385999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1621936482285339870923999 2432904723428009806385999)
      ·
        refine ⟨3649357085142014709578999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432904723428009806385999 3649357085142014709578999)
        ·
          refine ⟨5474035627713022064368499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649357085142014709578999 5474035627713022064368499)
          ·
            refine ⟨8211053441569533096552749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474035627713022064368499 8211053441569533096552749)
            ·
              refine ⟨3079145040588574911207281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8211053441569533096552749 3079145040588574911207281)
              ·
                refine ⟨2309358780441431183405461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079145040588574911207281 2309358780441431183405461)
                ·
                  refine ⟨108251192833192086722131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2309358780441431183405461 108251192833192086722131)
                  ·
                    rfl

theorem cell23_1897366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1897366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897366 prefixEnd_1897366 := by exact prefixLift 1897366
  have htrace : WordTrace (prefixWord ++ tailWord_1897366) baseStart_1897366 baseEnd_1897366 := by
    simpa [prefixWord, tailWord_1897366, baseEnd_1897366] using wordTrace_append hprefix tailTrace_1897366
  have hstable : (prefixWord ++ tailWord_1897366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897366).length < 2 ^ (prefixWord ++ tailWord_1897366).sum := by decide
  have hdescent : baseEnd_1897366 < baseStart_1897366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897385 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_1897385 : Nat := 118140960795 + 1897385 * 2 ^ 59
def prefixEnd_1897385 : Nat := 4983230072969 + 3 ^ 40 * 1897385 * 2
def baseEnd_1897385 : Nat := 974270491631164206161591

theorem tailTrace_1897385 : CollatzResearch.WordTrace tailWord_1897385 prefixEnd_1897385 974270491631164206161591 := by
  unfold tailWord_1897385
  simp only [CollatzResearch.WordTrace]
  refine ⟨69203316231105667404365609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46135544154070444936243739 69203316231105667404365609)
  ·
    refine ⟨51902487173329250553274207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69203316231105667404365609 51902487173329250553274207)
    ·
      refine ⟨77853730759993875829911311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51902487173329250553274207 77853730759993875829911311)
      ·
        refine ⟨116780596139990813744866967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77853730759993875829911311 116780596139990813744866967)
        ·
          refine ⟨175170894209986220617300451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116780596139990813744866967 175170894209986220617300451)
          ·
            refine ⟨262756341314979330925950677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175170894209986220617300451 262756341314979330925950677)
            ·
              refine ⟨6158351749569828068576969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 262756341314979330925950677 6158351749569828068576969)
              ·
                refine ⟨4618763812177371051432727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6158351749569828068576969 4618763812177371051432727)
                ·
                  refine ⟨6928145718266056577149091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618763812177371051432727 6928145718266056577149091)
                  ·
                    refine ⟨10392218577399084865723637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6928145718266056577149091 10392218577399084865723637)
                    ·
                      refine ⟨974270491631164206161591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10392218577399084865723637 974270491631164206161591)
                      ·
                        rfl

theorem cell23_1897385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_1897385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897385 prefixEnd_1897385 := by exact prefixLift 1897385
  have htrace : WordTrace (prefixWord ++ tailWord_1897385) baseStart_1897385 baseEnd_1897385 := by
    simpa [prefixWord, tailWord_1897385, baseEnd_1897385] using wordTrace_append hprefix tailTrace_1897385
  have hstable : (prefixWord ++ tailWord_1897385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897385).length < 2 ^ (prefixWord ++ tailWord_1897385).sum := by decide
  have hdescent : baseEnd_1897385 < baseStart_1897385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897395 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4]
def baseStart_1897395 : Nat := 118140960795 + 1897395 * 2 ^ 59
def prefixEnd_1897395 : Nat := 4983230072969 + 3 ^ 40 * 1897395 * 2
def baseEnd_1897395 : Nat := 974275626437709167036545

theorem tailTrace_1897395 : CollatzResearch.WordTrace tailWord_1897395 prefixEnd_1897395 974275626437709167036545 := by
  unfold tailWord_1897395
  simp only [CollatzResearch.WordTrace]
  refine ⟨69203680961069439112229639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46135787307379626074819759 69203680961069439112229639)
  ·
    refine ⟨103805521441604158668344459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69203680961069439112229639 103805521441604158668344459)
    ·
      refine ⟨155708282162406238002516689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103805521441604158668344459 155708282162406238002516689)
      ·
        refine ⟨116781211621804678501887517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155708282162406238002516689 116781211621804678501887517)
        ·
          refine ⟨43792954358176754438207819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 116781211621804678501887517 43792954358176754438207819)
          ·
            refine ⟨65689431537265131657311729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43792954358176754438207819 65689431537265131657311729)
            ·
              refine ⟨49267073652948848742983797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65689431537265131657311729 49267073652948848742983797)
              ·
                refine ⟨4618788154963954569654731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49267073652948848742983797 4618788154963954569654731)
                ·
                  refine ⟨6928182232445931854482097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4618788154963954569654731 6928182232445931854482097)
                  ·
                    refine ⟨5196136674334448890861573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6928182232445931854482097 5196136674334448890861573)
                    ·
                      refine ⟨974275626437709167036545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5196136674334448890861573 974275626437709167036545)
                      ·
                        rfl

theorem cell23_1897395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_1897395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897395 prefixEnd_1897395 := by exact prefixLift 1897395
  have htrace : WordTrace (prefixWord ++ tailWord_1897395) baseStart_1897395 baseEnd_1897395 := by
    simpa [prefixWord, tailWord_1897395, baseEnd_1897395] using wordTrace_append hprefix tailTrace_1897395
  have hstable : (prefixWord ++ tailWord_1897395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897395).length < 2 ^ (prefixWord ++ tailWord_1897395).sum := by decide
  have hdescent : baseEnd_1897395 < baseStart_1897395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897396 : List Nat := [2, 5, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1897396 : Nat := 118140960795 + 1897396 * 2 ^ 59
def prefixEnd_1897396 : Nat := 4983230072969 + 3 ^ 40 * 1897396 * 2
def baseEnd_1897396 : Nat := 324758713306121221041347

theorem tailTrace_1897396 : CollatzResearch.WordTrace tailWord_1897396 prefixEnd_1897396 324758713306121221041347 := by
  unfold tailWord_1897396
  simp only [CollatzResearch.WordTrace]
  refine ⟨34601858717032908141508021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46135811622710544188677361 34601858717032908141508021)
  ·
    refine ⟨3243924254721835138266377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34601858717032908141508021 3243924254721835138266377)
    ·
      refine ⟨2432943191041376353699783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3243924254721835138266377 2432943191041376353699783)
      ·
        refine ⟨3649414786562064530549675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2432943191041376353699783 3649414786562064530549675)
        ·
          refine ⟨5474122179843096795824513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649414786562064530549675 5474122179843096795824513)
          ·
            refine ⟨4105591634882322596868385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5474122179843096795824513 4105591634882322596868385)
            ·
              refine ⟨3079193726161741947651289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105591634882322596868385 3079193726161741947651289)
              ·
                refine ⟨2309395294621306460738467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3079193726161741947651289 2309395294621306460738467)
                ·
                  refine ⟨3464092941931959691107701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2309395294621306460738467 3464092941931959691107701)
                  ·
                    refine ⟨324758713306121221041347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3464092941931959691107701 324758713306121221041347)
                    ·
                      rfl

theorem cell23_1897396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1897396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897396 prefixEnd_1897396 := by exact prefixLift 1897396
  have htrace : WordTrace (prefixWord ++ tailWord_1897396) baseStart_1897396 baseEnd_1897396 := by
    simpa [prefixWord, tailWord_1897396, baseEnd_1897396] using wordTrace_append hprefix tailTrace_1897396
  have hstable : (prefixWord ++ tailWord_1897396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897396).length < 2 ^ (prefixWord ++ tailWord_1897396).sum := by decide
  have hdescent : baseEnd_1897396 < baseStart_1897396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897399 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 3, 2, 2]
def baseStart_1897399 : Nat := 118140960795 + 1897399 * 2 ^ 59
def prefixEnd_1897399 : Nat := 4983230072969 + 3 ^ 40 * 1897399 * 2
def baseEnd_1897399 : Nat := 974277680360327151386527

theorem tailTrace_1897399 : CollatzResearch.WordTrace tailWord_1897399 prefixEnd_1897399 974277680360327151386527 := by
  unfold tailWord_1897399
  simp only [CollatzResearch.WordTrace]
  refine ⟨69203826853054947795375251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46135884568703298530250167 69203826853054947795375251)
  ·
    refine ⟨103805740279582421693062877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69203826853054947795375251 103805740279582421693062877)
    ·
      refine ⟨38927152604843408134898579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103805740279582421693062877 38927152604843408134898579)
      ·
        refine ⟨58390728907265112202347869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38927152604843408134898579 58390728907265112202347869)
        ·
          refine ⟨21896523340224417075880451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58390728907265112202347869 21896523340224417075880451)
          ·
            refine ⟨32844785010336625613820677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21896523340224417075880451 32844785010336625613820677)
            ·
              refine ⟨6158397189438117302591377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32844785010336625613820677 6158397189438117302591377)
              ·
                refine ⟨4618797892078587976943533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6158397189438117302591377 4618797892078587976943533)
                ·
                  refine ⟨1732049209529470491353825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4618797892078587976943533 1732049209529470491353825)
                  ·
                    refine ⟨1299036907147102868515369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1732049209529470491353825 1299036907147102868515369)
                    ·
                      refine ⟨974277680360327151386527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299036907147102868515369 974277680360327151386527)
                      ·
                        rfl

theorem cell23_1897399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 3, 2, 2].length) (baseStart_1897399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897399 prefixEnd_1897399 := by exact prefixLift 1897399
  have htrace : WordTrace (prefixWord ++ tailWord_1897399) baseStart_1897399 baseEnd_1897399 := by
    simpa [prefixWord, tailWord_1897399, baseEnd_1897399] using wordTrace_append hprefix tailTrace_1897399
  have hstable : (prefixWord ++ tailWord_1897399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897399).length < 2 ^ (prefixWord ++ tailWord_1897399).sum := by decide
  have hdescent : baseEnd_1897399 < baseStart_1897399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897489 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 4, 2, 2]
def baseStart_1897489 : Nat := 118140960795 + 1897489 * 2 ^ 59
def prefixEnd_1897489 : Nat := 4983230072969 + 3 ^ 40 * 1897489 * 2
def baseEnd_1897489 : Nat := 974323893619231799261113

theorem tailTrace_1897489 : CollatzResearch.WordTrace tailWord_1897489 prefixEnd_1897489 974323893619231799261113 := by
  unfold tailWord_1897489
  simp only [CollatzResearch.WordTrace]
  refine ⟨69207109422728893166151521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46138072948485928777434347 69207109422728893166151521)
  ·
    refine ⟨51905332067046669874613641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69207109422728893166151521 51905332067046669874613641)
    ·
      refine ⟨38928999050285002405960231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51905332067046669874613641 38928999050285002405960231)
      ·
        refine ⟨58393498575427503608940347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38928999050285002405960231 58393498575427503608940347)
        ·
          refine ⟨87590247863141255413410521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58393498575427503608940347 87590247863141255413410521)
          ·
            refine ⟨65692685897355941560057891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87590247863141255413410521 65692685897355941560057891)
            ·
              refine ⟨98539028846033912340086837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65692685897355941560057891 98539028846033912340086837)
              ·
                refine ⟨9238033954315679281883141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98539028846033912340086837 9238033954315679281883141)
                ·
                  refine ⟨1732131366434189865353089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9238033954315679281883141 1732131366434189865353089)
                  ·
                    refine ⟨1299098524825642399014817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1732131366434189865353089 1299098524825642399014817)
                    ·
                      refine ⟨974323893619231799261113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299098524825642399014817 974323893619231799261113)
                      ·
                        rfl

theorem cell23_1897489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_1897489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897489 prefixEnd_1897489 := by exact prefixLift 1897489
  have htrace : WordTrace (prefixWord ++ tailWord_1897489) baseStart_1897489 baseEnd_1897489 := by
    simpa [prefixWord, tailWord_1897489, baseEnd_1897489] using wordTrace_append hprefix tailTrace_1897489
  have hstable : (prefixWord ++ tailWord_1897489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897489).length < 2 ^ (prefixWord ++ tailWord_1897489).sum := by decide
  have hdescent : baseEnd_1897489 < baseStart_1897489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897506 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_1897506 : Nat := 118140960795 + 1897506 * 2 ^ 59
def prefixEnd_1897506 : Nat := 4983230072969 + 3 ^ 40 * 1897506 * 2
def baseEnd_1897506 : Nat := 974332622790358232748535

theorem tailTrace_1897506 : CollatzResearch.WordTrace tailWord_1897506 prefixEnd_1897506 974332622790358232748535 := by
  unfold tailWord_1897506
  simp only [CollatzResearch.WordTrace]
  refine ⟨17301932365916826267380093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46138486309111536713013581 17301932365916826267380093)
  ·
    refine ⟨6488224637218809850267535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17301932365916826267380093 6488224637218809850267535)
    ·
      refine ⟨9732336955828214775401303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488224637218809850267535 9732336955828214775401303)
      ·
        refine ⟨14598505433742322163101955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9732336955828214775401303 14598505433742322163101955)
        ·
          refine ⟨21897758150613483244652933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14598505433742322163101955 21897758150613483244652933)
          ·
            refine ⟨4105829653240028108372425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21897758150613483244652933 4105829653240028108372425)
            ·
              refine ⟨3079372239930021081279319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4105829653240028108372425 3079372239930021081279319)
              ·
                refine ⟨4619058359895031621918979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3079372239930021081279319 4619058359895031621918979)
                ·
                  refine ⟨6928587539842547432878469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4619058359895031621918979 6928587539842547432878469)
                  ·
                    refine ⟨1299110163720477643664713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6928587539842547432878469 1299110163720477643664713)
                    ·
                      refine ⟨974332622790358232748535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1299110163720477643664713 974332622790358232748535)
                      ·
                        rfl

theorem cell23_1897506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_1897506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897506 prefixEnd_1897506 := by exact prefixLift 1897506
  have htrace : WordTrace (prefixWord ++ tailWord_1897506) baseStart_1897506 baseEnd_1897506 := by
    simpa [prefixWord, tailWord_1897506, baseEnd_1897506] using wordTrace_append hprefix tailTrace_1897506
  have hstable : (prefixWord ++ tailWord_1897506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897506).length < 2 ^ (prefixWord ++ tailWord_1897506).sum := by decide
  have hdescent : baseEnd_1897506 < baseStart_1897506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897522 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_1897522 : Nat := 118140960795 + 1897522 * 2 ^ 59
def prefixEnd_1897522 : Nat := 4983230072969 + 3 ^ 40 * 1897522 * 2
def baseEnd_1897522 : Nat := 974340838480830170148461

theorem tailTrace_1897522 : CollatzResearch.WordTrace tailWord_1897522 prefixEnd_1897522 974340838480830170148461 := by
  unfold tailWord_1897522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17302078257902334950525705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46138875354406226534735213 17302078257902334950525705)
  ·
    refine ⟨12976558693426751212894279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17302078257902334950525705 12976558693426751212894279)
    ·
      refine ⟨19464838040140126819341419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12976558693426751212894279 19464838040140126819341419)
      ·
        refine ⟨29197257060210190229012129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19464838040140126819341419 29197257060210190229012129)
        ·
          refine ⟨21897942795157642671759097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29197257060210190229012129 21897942795157642671759097)
          ·
            refine ⟨16423457096368232003819323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21897942795157642671759097 16423457096368232003819323)
            ·
              refine ⟨24635185644552348005728985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16423457096368232003819323 24635185644552348005728985)
              ·
                refine ⟨18476389233414261004296739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24635185644552348005728985 18476389233414261004296739)
                ·
                  refine ⟨27714583850121391506445109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18476389233414261004296739 27714583850121391506445109)
                  ·
                    refine ⟨2598242235948880453729229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27714583850121391506445109 2598242235948880453729229)
                    ·
                      refine ⟨974340838480830170148461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2598242235948880453729229 974340838480830170148461)
                      ·
                        rfl

theorem cell23_1897522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_1897522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897522 prefixEnd_1897522 := by exact prefixLift 1897522
  have htrace : WordTrace (prefixWord ++ tailWord_1897522) baseStart_1897522 baseEnd_1897522 := by
    simpa [prefixWord, tailWord_1897522, baseEnd_1897522] using wordTrace_append hprefix tailTrace_1897522
  have hstable : (prefixWord ++ tailWord_1897522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897522).length < 2 ^ (prefixWord ++ tailWord_1897522).sum := by decide
  have hdescent : baseEnd_1897522 < baseStart_1897522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897529 : List Nat := [1, 2, 1, 5, 2, 1, 1, 5, 5]
def baseStart_1897529 : Nat := 118140960795 + 1897529 * 2 ^ 59
def prefixEnd_1897529 : Nat := 4983230072969 + 3 ^ 40 * 1897529 * 2
def baseEnd_1897529 : Nat := 108260492538379071417881

theorem tailTrace_1897529 : CollatzResearch.WordTrace tailWord_1897529 prefixEnd_1897529 108260492538379071417881 := by
  unfold tailWord_1897529
  simp only [CollatzResearch.WordTrace]
  refine ⟨69208568342583979997607641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46139045561722653331738427 69208568342583979997607641)
  ·
    refine ⟨51906426256937984998205731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69208568342583979997607641 51906426256937984998205731)
    ·
      refine ⟨77859639385406977497308597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51906426256937984998205731 77859639385406977497308597)
      ·
        refine ⟨7299341192381904140372681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77859639385406977497308597 7299341192381904140372681)
        ·
          refine ⟨5474505894286428105279511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7299341192381904140372681 5474505894286428105279511)
          ·
            refine ⟨8211758841429642157919267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5474505894286428105279511 8211758841429642157919267)
            ·
              refine ⟨12317638262144463236878901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8211758841429642157919267 12317638262144463236878901)
              ·
                refine ⟨1154778587076043428457397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12317638262144463236878901 1154778587076043428457397)
                ·
                  refine ⟨108260492538379071417881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1154778587076043428457397 108260492538379071417881)
                  ·
                    rfl

theorem cell23_1897529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 5, 5].length) (baseStart_1897529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897529 prefixEnd_1897529 := by exact prefixLift 1897529
  have htrace : WordTrace (prefixWord ++ tailWord_1897529) baseStart_1897529 baseEnd_1897529 := by
    simpa [prefixWord, tailWord_1897529, baseEnd_1897529] using wordTrace_append hprefix tailTrace_1897529
  have hstable : (prefixWord ++ tailWord_1897529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897529).length < 2 ^ (prefixWord ++ tailWord_1897529).sum := by decide
  have hdescent : baseEnd_1897529 < baseStart_1897529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1897555 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 2, 8]
def baseStart_1897555 : Nat := 118140960795 + 1897555 * 2 ^ 59
def prefixEnd_1897555 : Nat := 4983230072969 + 3 ^ 40 * 1897555 * 2
def baseEnd_1897555 : Nat := 324785927780809513678603

theorem tailTrace_1897555 : CollatzResearch.WordTrace tailWord_1897555 prefixEnd_1897555 324785927780809513678603 := by
  unfold tailWord_1897555
  simp only [CollatzResearch.WordTrace]
  refine ⟨69209516640489786438054119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46139677760326524292036079 69209516640489786438054119)
  ·
    refine ⟨103814274960734679657081179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69209516640489786438054119 103814274960734679657081179)
    ·
      refine ⟨155721412441102019485621769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103814274960734679657081179 155721412441102019485621769)
      ·
        refine ⟨116791059330826514614216327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 155721412441102019485621769 116791059330826514614216327)
        ·
          refine ⟨175186588996239771921324491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116791059330826514614216327 175186588996239771921324491)
          ·
            refine ⟨262779883494359657881986737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 175186588996239771921324491 262779883494359657881986737)
            ·
              refine ⟨197084912620769743411490053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262779883494359657881986737 197084912620769743411490053)
              ·
                refine ⟨36953421116394326889654385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197084912620769743411490053 36953421116394326889654385)
                ·
                  refine ⟨27715065837295745167240789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36953421116394326889654385 27715065837295745167240789)
                  ·
                    refine ⟨324785927780809513678603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27715065837295745167240789 324785927780809513678603)
                    ·
                      rfl

theorem cell23_1897555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_1897555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1897555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1897555 prefixEnd_1897555 := by exact prefixLift 1897555
  have htrace : WordTrace (prefixWord ++ tailWord_1897555) baseStart_1897555 baseEnd_1897555 := by
    simpa [prefixWord, tailWord_1897555, baseEnd_1897555] using wordTrace_append hprefix tailTrace_1897555
  have hstable : (prefixWord ++ tailWord_1897555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1897555).length < 2 ^ (prefixWord ++ tailWord_1897555).sum := by decide
  have hdescent : baseEnd_1897555 < baseStart_1897555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1897555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
