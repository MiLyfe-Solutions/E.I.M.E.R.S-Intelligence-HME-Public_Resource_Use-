import V185TrunkScan23Chunk1149

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6811541 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 3]
def baseStart_6811541 : Nat := 118140960795 + 6811541 * 2 ^ 59
def prefixEnd_6811541 : Nat := 4983230072969 + 3 ^ 40 * 6811541 * 2
def baseEnd_6811541 : Nat := 3497594530807039548211799

theorem tailTrace_6811541 : CollatzResearch.WordTrace tailWord_6811541 prefixEnd_6811541 3497594530807039548211799 := by
  unfold tailWord_6811541
  simp only [CollatzResearch.WordTrace]
  refine ⟨248437310215957750431386477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165624873477305166954257651 248437310215957750431386477)
  ·
    refine ⟨93163991330984156411769929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248437310215957750431386477 93163991330984156411769929)
    ·
      refine ⟨69872993498238117308827447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93163991330984156411769929 69872993498238117308827447)
      ·
        refine ⟨104809490247357175963241171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69872993498238117308827447 104809490247357175963241171)
        ·
          refine ⟨157214235371035763944861757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104809490247357175963241171 157214235371035763944861757)
          ·
            refine ⟨58955338264138411479323159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157214235371035763944861757 58955338264138411479323159)
            ·
              refine ⟨88433007396207617218984739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58955338264138411479323159 88433007396207617218984739)
              ·
                refine ⟨132649511094311425828477109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88433007396207617218984739 132649511094311425828477109)
                ·
                  refine ⟨12435891665091696171419729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132649511094311425828477109 12435891665091696171419729)
                  ·
                    refine ⟨9326918748818772128564797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12435891665091696171419729 9326918748818772128564797)
                    ·
                      refine ⟨3497594530807039548211799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326918748818772128564797 3497594530807039548211799)
                      ·
                        rfl

theorem cell23_6811541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_6811541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811541 prefixEnd_6811541 := by exact prefixLift 6811541
  have htrace : WordTrace (prefixWord ++ tailWord_6811541) baseStart_6811541 baseEnd_6811541 := by
    simpa [prefixWord, tailWord_6811541, baseEnd_6811541] using wordTrace_append hprefix tailTrace_6811541
  have hstable : (prefixWord ++ tailWord_6811541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811541).length < 2 ^ (prefixWord ++ tailWord_6811541).sum := by decide
  have hdescent : baseEnd_6811541 < baseStart_6811541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811548 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6811548 : Nat := 118140960795 + 6811548 * 2 ^ 59
def prefixEnd_6811548 : Nat := 4983230072969 + 3 ^ 40 * 6811548 * 2
def baseEnd_6811548 : Nat := 1165866041723873673608089

theorem tailTrace_6811548 : CollatzResearch.WordTrace tailWord_6811548 prefixEnd_6811548 1165866041723873673608089 := by
  unfold tailWord_6811548
  simp only [CollatzResearch.WordTrace]
  refine ⟨124218782763466195313445649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165625043684621593751260865 124218782763466195313445649)
  ·
    refine ⟨93164087072599646485084237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124218782763466195313445649 93164087072599646485084237)
    ·
      refine ⟨34936532652224867431906589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93164087072599646485084237 34936532652224867431906589)
      ·
        refine ⟨13101199744584325286964971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34936532652224867431906589 13101199744584325286964971)
        ·
          refine ⟨19651799616876487930447457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101199744584325286964971 19651799616876487930447457)
          ·
            refine ⟨14738849712657365947835593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19651799616876487930447457 14738849712657365947835593)
            ·
              refine ⟨11054137284493024460876695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14738849712657365947835593 11054137284493024460876695)
              ·
                refine ⟨16581205926739536691315043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054137284493024460876695 16581205926739536691315043)
                ·
                  refine ⟨24871808890109305036972565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16581205926739536691315043 24871808890109305036972565)
                  ·
                    refine ⟨1165866041723873673608089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24871808890109305036972565 1165866041723873673608089)
                    ·
                      rfl

theorem cell23_6811548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6811548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811548 prefixEnd_6811548 := by exact prefixLift 6811548
  have htrace : WordTrace (prefixWord ++ tailWord_6811548) baseStart_6811548 baseEnd_6811548 := by
    simpa [prefixWord, tailWord_6811548, baseEnd_6811548] using wordTrace_append hprefix tailTrace_6811548
  have hstable : (prefixWord ++ tailWord_6811548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811548).length < 2 ^ (prefixWord ++ tailWord_6811548).sum := by decide
  have hdescent : baseEnd_6811548 < baseStart_6811548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811571 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 3]
def baseStart_6811571 : Nat := 118140960795 + 6811571 * 2 ^ 59
def prefixEnd_6811571 : Nat := 4983230072969 + 3 ^ 40 * 6811571 * 2
def baseEnd_6811571 : Nat := 3497609935226674430836661

theorem tailTrace_6811571 : CollatzResearch.WordTrace tailWord_6811571 prefixEnd_6811571 3497609935226674430836661 := by
  unfold tailWord_6811571
  simp only [CollatzResearch.WordTrace]
  refine ⟨248438404405849065554978567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165625602937232710369985711 248438404405849065554978567)
  ·
    refine ⟨372657606608773598332467851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248438404405849065554978567 372657606608773598332467851)
    ·
      refine ⟨558986409913160397498701777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372657606608773598332467851 558986409913160397498701777)
      ·
        refine ⟨419239807434870298124026333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558986409913160397498701777 419239807434870298124026333)
        ·
          refine ⟨157214927788076361796509875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419239807434870298124026333 157214927788076361796509875)
          ·
            refine ⟨235822391682114542694764813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157214927788076361796509875 235822391682114542694764813)
            ·
              refine ⟨88433396880792953510536805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235822391682114542694764813 88433396880792953510536805)
              ·
                refine ⟨16581261915148678783225651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88433396880792953510536805 16581261915148678783225651)
                ·
                  refine ⟨24871892872723018174838477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16581261915148678783225651 24871892872723018174838477)
                  ·
                    refine ⟨9326959827271131815564429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24871892872723018174838477 9326959827271131815564429)
                    ·
                      refine ⟨3497609935226674430836661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9326959827271131815564429 3497609935226674430836661)
                      ·
                        rfl

theorem cell23_6811571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_6811571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811571 prefixEnd_6811571 := by exact prefixLift 6811571
  have htrace : WordTrace (prefixWord ++ tailWord_6811571) baseStart_6811571 baseEnd_6811571 := by
    simpa [prefixWord, tailWord_6811571, baseEnd_6811571] using wordTrace_append hprefix tailTrace_6811571
  have hstable : (prefixWord ++ tailWord_6811571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811571).length < 2 ^ (prefixWord ++ tailWord_6811571).sum := by decide
  have hdescent : baseEnd_6811571 < baseStart_6811571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811572 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6811572 : Nat := 118140960795 + 6811572 * 2 ^ 59
def prefixEnd_6811572 : Nat := 4983230072969 + 3 ^ 40 * 6811572 * 2
def baseEnd_6811572 : Nat := 3497610448707328926924157

theorem tailTrace_6811572 : CollatzResearch.WordTrace tailWord_6811572 prefixEnd_6811572 3497610448707328926924157 := by
  unfold tailWord_6811572
  simp only [CollatzResearch.WordTrace]
  refine ⟨124219220439422721362882485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165625627252563628483843313 124219220439422721362882485)
  ·
    refine ⟨11645551916195880127770233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124219220439422721362882485 11645551916195880127770233)
    ·
      refine ⟨8734163937146910095827675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11645551916195880127770233 8734163937146910095827675)
      ·
        refine ⟨13101245905720365143741513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8734163937146910095827675 13101245905720365143741513)
        ·
          refine ⟨9825934429290273857806135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13101245905720365143741513 9825934429290273857806135)
          ·
            refine ⟨14738901643935410786709203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9825934429290273857806135 14738901643935410786709203)
            ·
              refine ⟨22108352465903116180063805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14738901643935410786709203 22108352465903116180063805)
              ·
                refine ⟨8290632174713668567523927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22108352465903116180063805 8290632174713668567523927)
                ·
                  refine ⟨12435948262070502851285891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290632174713668567523927 12435948262070502851285891)
                  ·
                    refine ⟨18653922393105754276928837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12435948262070502851285891 18653922393105754276928837)
                    ·
                      refine ⟨3497610448707328926924157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18653922393105754276928837 3497610448707328926924157)
                      ·
                        rfl

theorem cell23_6811572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6811572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811572 prefixEnd_6811572 := by exact prefixLift 6811572
  have htrace : WordTrace (prefixWord ++ tailWord_6811572) baseStart_6811572 baseEnd_6811572 := by
    simpa [prefixWord, tailWord_6811572, baseEnd_6811572] using wordTrace_append hprefix tailTrace_6811572
  have hstable : (prefixWord ++ tailWord_6811572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811572).length < 2 ^ (prefixWord ++ tailWord_6811572).sum := by decide
  have hdescent : baseEnd_6811572 < baseStart_6811572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811602 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6811602 : Nat := 118140960795 + 6811602 * 2 ^ 59
def prefixEnd_6811602 : Nat := 4983230072969 + 3 ^ 40 * 6811602 * 2
def baseEnd_6811602 : Nat := 3497625853126963809549019

theorem tailTrace_6811602 : CollatzResearch.WordTrace tailWord_6811602 prefixEnd_6811602 3497625853126963809549019 := by
  unfold tailWord_6811602
  simp only [CollatzResearch.WordTrace]
  refine ⟨62109883767184189462339265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165626356712491171899571373 62109883767184189462339265)
  ·
    refine ⟨46582412825388142096754449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62109883767184189462339265 46582412825388142096754449)
    ·
      refine ⟨34936809619041106572565837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46582412825388142096754449 34936809619041106572565837)
      ·
        refine ⟨13101303607140414964712189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34936809619041106572565837 13101303607140414964712189)
        ·
          refine ⟨4912988852677655611767071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13101303607140414964712189 4912988852677655611767071)
          ·
            refine ⟨7369483279016483417650607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912988852677655611767071 7369483279016483417650607)
            ·
              refine ⟨11054224918524725126475911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369483279016483417650607 11054224918524725126475911)
              ·
                refine ⟨16581337377787087689713867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054224918524725126475911 16581337377787087689713867)
                ·
                  refine ⟨24872006066680631534570801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16581337377787087689713867 24872006066680631534570801)
                  ·
                    refine ⟨18654004550010473650928101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24872006066680631534570801 18654004550010473650928101)
                    ·
                      refine ⟨3497625853126963809549019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18654004550010473650928101 3497625853126963809549019)
                      ·
                        rfl

theorem cell23_6811602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6811602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811602 prefixEnd_6811602 := by exact prefixLift 6811602
  have htrace : WordTrace (prefixWord ++ tailWord_6811602) baseStart_6811602 baseEnd_6811602 := by
    simpa [prefixWord, tailWord_6811602, baseEnd_6811602] using wordTrace_append hprefix tailTrace_6811602
  have hstable : (prefixWord ++ tailWord_6811602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811602).length < 2 ^ (prefixWord ++ tailWord_6811602).sum := by decide
  have hdescent : baseEnd_6811602 < baseStart_6811602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811605 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 3]
def baseStart_6811605 : Nat := 118140960795 + 6811605 * 2 ^ 59
def prefixEnd_6811605 : Nat := 4983230072969 + 3 ^ 40 * 6811605 * 2
def baseEnd_6811605 : Nat := 3497627393568927297811505

theorem tailTrace_6811605 : CollatzResearch.WordTrace tailWord_6811605 prefixEnd_6811605 3497627393568927297811505 := by
  unfold tailWord_6811605
  simp only [CollatzResearch.WordTrace]
  refine ⟨248439644487725889361716269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165626429658483926241144179 248439644487725889361716269)
  ·
    refine ⟨93164866682897208510643601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248439644487725889361716269 93164866682897208510643601)
    ·
      refine ⟨69873650012172906382982701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93164866682897208510643601 69873650012172906382982701)
      ·
        refine ⟨26202618754564839893618513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69873650012172906382982701 26202618754564839893618513)
        ·
          refine ⟨19651964065923629920213885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26202618754564839893618513 19651964065923629920213885)
          ·
            refine ⟨7369486524721361220080207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19651964065923629920213885 7369486524721361220080207)
            ·
              refine ⟨11054229787082041830120311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369486524721361220080207 11054229787082041830120311)
              ·
                refine ⟨16581344680623062745180467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054229787082041830120311 16581344680623062745180467)
                ·
                  refine ⟨24872017020934594117770701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16581344680623062745180467 24872017020934594117770701)
                  ·
                    refine ⟨9327006382850472794164013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24872017020934594117770701 9327006382850472794164013)
                    ·
                      refine ⟨3497627393568927297811505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9327006382850472794164013 3497627393568927297811505)
                      ·
                        rfl

theorem cell23_6811605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_6811605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811605 prefixEnd_6811605 := by exact prefixLift 6811605
  have htrace : WordTrace (prefixWord ++ tailWord_6811605) baseStart_6811605 baseEnd_6811605 := by
    simpa [prefixWord, tailWord_6811605, baseEnd_6811605] using wordTrace_append hprefix tailTrace_6811605
  have hstable : (prefixWord ++ tailWord_6811605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811605).length < 2 ^ (prefixWord ++ tailWord_6811605).sum := by decide
  have hdescent : baseEnd_6811605 < baseStart_6811605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811615 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 1, 3, 2]
def baseStart_6811615 : Nat := 118140960795 + 6811615 * 2 ^ 59
def prefixEnd_6811615 : Nat := 4983230072969 + 3 ^ 40 * 6811615 * 2
def baseEnd_6811615 : Nat := 3497632528375472258686459

theorem tailTrace_6811615 : CollatzResearch.WordTrace tailWord_6811615 prefixEnd_6811615 3497632528375472258686459 := by
  unfold tailWord_6811615
  simp only [CollatzResearch.WordTrace]
  refine ⟨248440009217689661069580299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165626672811793107379720199 248440009217689661069580299)
  ·
    refine ⟨372660013826534491604370449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248440009217689661069580299 372660013826534491604370449)
    ·
      refine ⟨279495010369900868703277837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372660013826534491604370449 279495010369900868703277837)
      ·
        refine ⟨104810628888712825763729189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279495010369900868703277837 104810628888712825763729189)
        ·
          refine ⟨19651992916633654830699223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104810628888712825763729189 19651992916633654830699223)
          ·
            refine ⟨29477989374950482246048835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19651992916633654830699223 29477989374950482246048835)
            ·
              refine ⟨44216984062425723369073253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29477989374950482246048835 44216984062425723369073253)
              ·
                refine ⟨8290684511704823131701235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44216984062425723369073253 8290684511704823131701235)
                ·
                  refine ⟨12436026767557234697551853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290684511704823131701235 12436026767557234697551853)
                  ·
                    refine ⟨4663510037833963011581945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12436026767557234697551853 4663510037833963011581945)
                    ·
                      refine ⟨3497632528375472258686459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663510037833963011581945 3497632528375472258686459)
                      ·
                        rfl

theorem cell23_6811615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_6811615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811615 prefixEnd_6811615 := by exact prefixLift 6811615
  have htrace : WordTrace (prefixWord ++ tailWord_6811615) baseStart_6811615 baseEnd_6811615 := by
    simpa [prefixWord, tailWord_6811615, baseEnd_6811615] using wordTrace_append hprefix tailTrace_6811615
  have hstable : (prefixWord ++ tailWord_6811615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811615).length < 2 ^ (prefixWord ++ tailWord_6811615).sum := by decide
  have hdescent : baseEnd_6811615 < baseStart_6811615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811628 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 1, 4, 2]
def baseStart_6811628 : Nat := 118140960795 + 6811628 * 2 ^ 59
def prefixEnd_6811628 : Nat := 4983230072969 + 3 ^ 40 * 6811628 * 2
def baseEnd_6811628 : Nat := 3497639203623980707823899

theorem tailTrace_6811628 : CollatzResearch.WordTrace tailWord_6811628 prefixEnd_6811628 3497639203623980707823899 := by
  unfold tailWord_6811628
  simp only [CollatzResearch.WordTrace]
  refine ⟨124220241683321282144901769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165626988911095042859869025 124220241683321282144901769)
  ·
    refine ⟨93165181262490961608676327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124220241683321282144901769 93165181262490961608676327)
    ·
      refine ⟨139747771893736442413014491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93165181262490961608676327 139747771893736442413014491)
      ·
        refine ⟨209621657840604663619521737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139747771893736442413014491 209621657840604663619521737)
        ·
          refine ⟨157216243380453497714641303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209621657840604663619521737 157216243380453497714641303)
          ·
            refine ⟨235824365070680246571961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157216243380453497714641303 235824365070680246571961955)
            ·
              refine ⟨353736547606020369857942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235824365070680246571961955 353736547606020369857942933)
              ·
                refine ⟨16581400669032204837091075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 353736547606020369857942933 16581400669032204837091075)
                ·
                  refine ⟨24872101003548307255636613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16581400669032204837091075 24872101003548307255636613)
                  ·
                    refine ⟨4663518938165307610431865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24872101003548307255636613 4663518938165307610431865)
                    ·
                      refine ⟨3497639203623980707823899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663518938165307610431865 3497639203623980707823899)
                      ·
                        rfl

theorem cell23_6811628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 4, 2].length) (baseStart_6811628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811628 prefixEnd_6811628 := by exact prefixLift 6811628
  have htrace : WordTrace (prefixWord ++ tailWord_6811628) baseStart_6811628 baseEnd_6811628 := by
    simpa [prefixWord, tailWord_6811628, baseEnd_6811628] using wordTrace_append hprefix tailTrace_6811628
  have hstable : (prefixWord ++ tailWord_6811628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811628).length < 2 ^ (prefixWord ++ tailWord_6811628).sum := by decide
  have hdescent : baseEnd_6811628 < baseStart_6811628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811631 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_6811631 : Nat := 118140960795 + 6811631 * 2 ^ 59
def prefixEnd_6811631 : Nat := 4983230072969 + 3 ^ 40 * 6811631 * 2
def baseEnd_6811631 : Nat := 3497640744065944196086385

theorem tailTrace_6811631 : CollatzResearch.WordTrace tailWord_6811631 prefixEnd_6811631 3497640744065944196086385 := by
  unfold tailWord_6811631
  simp only [CollatzResearch.WordTrace]
  refine ⟨248440592785631695802162747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165627061857087797201441831 248440592785631695802162747)
  ·
    refine ⟨372660889178447543703244121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248440592785631695802162747 372660889178447543703244121)
    ·
      refine ⟨279495666883835657777433091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372660889178447543703244121 279495666883835657777433091)
      ·
        refine ⟨419243500325753486666149637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279495666883835657777433091 419243500325753486666149637)
        ·
          refine ⟨78608156311078778749903057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419243500325753486666149637 78608156311078778749903057)
          ·
            refine ⟨58956117233309084062427293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78608156311078778749903057 58956117233309084062427293)
            ·
              refine ⟨22108543962490906523410235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58956117233309084062427293 22108543962490906523410235)
              ·
                refine ⟨33162815943736359785115353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22108543962490906523410235 33162815943736359785115353)
                ·
                  refine ⟨24872111957802269838836515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33162815943736359785115353 24872111957802269838836515)
                  ·
                    refine ⟨37308167936703404758254773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24872111957802269838836515 37308167936703404758254773)
                    ·
                      refine ⟨3497640744065944196086385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37308167936703404758254773 3497640744065944196086385)
                      ·
                        rfl

theorem cell23_6811631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_6811631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811631 prefixEnd_6811631 := by exact prefixLift 6811631
  have htrace : WordTrace (prefixWord ++ tailWord_6811631) baseStart_6811631 baseEnd_6811631 := by
    simpa [prefixWord, tailWord_6811631, baseEnd_6811631] using wordTrace_append hprefix tailTrace_6811631
  have hstable : (prefixWord ++ tailWord_6811631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811631).length < 2 ^ (prefixWord ++ tailWord_6811631).sum := by decide
  have hdescent : baseEnd_6811631 < baseStart_6811631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811645 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 4, 2, 2]
def baseStart_6811645 : Nat := 118140960795 + 6811645 * 2 ^ 59
def prefixEnd_6811645 : Nat := 4983230072969 + 3 ^ 40 * 6811645 * 2
def baseEnd_6811645 : Nat := 3497647932795107141311321

theorem tailTrace_6811645 : CollatzResearch.WordTrace tailWord_6811645 prefixEnd_6811645 3497647932795107141311321 := by
  unfold tailWord_6811645
  simp only [CollatzResearch.WordTrace]
  refine ⟨248441103407580976193172389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165627402271720650795448259 248441103407580976193172389)
  ·
    refine ⟨46582706888921433036219823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248441103407580976193172389 46582706888921433036219823)
    ·
      refine ⟨69874060333382149554329735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46582706888921433036219823 69874060333382149554329735)
      ·
        refine ⟨104811090500073224331494603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69874060333382149554329735 104811090500073224331494603)
        ·
          refine ⟨157216635750109836497241905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104811090500073224331494603 157216635750109836497241905)
          ·
            refine ⟨117912476812582377372931429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157216635750109836497241905 117912476812582377372931429)
            ·
              refine ⟨22108589402359195757424643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117912476812582377372931429 22108589402359195757424643)
              ·
                refine ⟨33162884103538793636136965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22108589402359195757424643 33162884103538793636136965)
                ·
                  refine ⟨6218040769413523806775681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33162884103538793636136965 6218040769413523806775681)
                  ·
                    refine ⟨4663530577060142855081761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218040769413523806775681 4663530577060142855081761)
                    ·
                      refine ⟨3497647932795107141311321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663530577060142855081761 3497647932795107141311321)
                      ·
                        rfl

theorem cell23_6811645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 2, 2].length) (baseStart_6811645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811645 prefixEnd_6811645 := by exact prefixLift 6811645
  have htrace : WordTrace (prefixWord ++ tailWord_6811645) baseStart_6811645 baseEnd_6811645 := by
    simpa [prefixWord, tailWord_6811645, baseEnd_6811645] using wordTrace_append hprefix tailTrace_6811645
  have hstable : (prefixWord ++ tailWord_6811645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811645).length < 2 ^ (prefixWord ++ tailWord_6811645).sum := by decide
  have hdescent : baseEnd_6811645 < baseStart_6811645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811662 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_6811662 : Nat := 118140960795 + 6811662 * 2 ^ 59
def prefixEnd_6811662 : Nat := 4983230072969 + 3 ^ 40 * 6811662 * 2
def baseEnd_6811662 : Nat := 3497656661966233574798743

theorem tailTrace_6811662 : CollatzResearch.WordTrace tailWord_6811662 prefixEnd_6811662 3497656661966233574798743 := by
  unfold tailWord_6811662
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055215431064923512067655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165627815632346258731027493 31055215431064923512067655)
  ·
    refine ⟨46582823146597385268101483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31055215431064923512067655 46582823146597385268101483)
    ·
      refine ⟨69874234719896077902152225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46582823146597385268101483 69874234719896077902152225)
      ·
        refine ⟨52405676039922058426614169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69874234719896077902152225 52405676039922058426614169)
        ·
          refine ⟨39304257029941543819960627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52405676039922058426614169 39304257029941543819960627)
          ·
            refine ⟨58956385544912315729940941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39304257029941543819960627 58956385544912315729940941)
            ·
              refine ⟨22108644579342118398727853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58956385544912315729940941 22108644579342118398727853)
              ·
                refine ⟨8290741717253294399522945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22108644579342118398727853 8290741717253294399522945)
                ·
                  refine ⟨6218056287939970799642209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8290741717253294399522945 6218056287939970799642209)
                  ·
                    refine ⟨4663542215954978099731657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218056287939970799642209 4663542215954978099731657)
                    ·
                      refine ⟨3497656661966233574798743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663542215954978099731657 3497656661966233574798743)
                      ·
                        rfl

theorem cell23_6811662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_6811662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811662 prefixEnd_6811662 := by exact prefixLift 6811662
  have htrace : WordTrace (prefixWord ++ tailWord_6811662) baseStart_6811662 baseEnd_6811662 := by
    simpa [prefixWord, tailWord_6811662, baseEnd_6811662] using wordTrace_append hprefix tailTrace_6811662
  have hstable : (prefixWord ++ tailWord_6811662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811662).length < 2 ^ (prefixWord ++ tailWord_6811662).sum := by decide
  have hdescent : baseEnd_6811662 < baseStart_6811662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811698 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 2, 5]
def baseStart_6811698 : Nat := 118140960795 + 6811698 * 2 ^ 59
def prefixEnd_6811698 : Nat := 4983230072969 + 3 ^ 40 * 6811698 * 2
def baseEnd_6811698 : Nat := 1165891715756598477982859

theorem tailTrace_6811698 : CollatzResearch.WordTrace tailWord_6811698 prefixEnd_6811698 1165891715756598477982859 := by
  unfold tailWord_6811698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62110759119097241561212937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165628690984259310829901165 62110759119097241561212937)
  ·
    refine ⟨46583069339322931170909703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62110759119097241561212937 46583069339322931170909703)
    ·
      refine ⟨69874604008984396756364555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46583069339322931170909703 69874604008984396756364555)
      ·
        refine ⟨104811906013476595134546833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69874604008984396756364555 104811906013476595134546833)
        ·
          refine ⟨78608929510107446350910125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104811906013476595134546833 78608929510107446350910125)
          ·
            refine ⟨29478348566290292381591297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78608929510107446350910125 29478348566290292381591297)
            ·
              refine ⟨22108761424717719286193473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29478348566290292381591297 22108761424717719286193473)
              ·
                refine ⟨16581571068538289464645105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22108761424717719286193473 16581571068538289464645105)
                ·
                  refine ⟨12436178301403717098483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16581571068538289464645105 12436178301403717098483829)
                  ·
                    refine ⟨1165891715756598477982859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12436178301403717098483829 1165891715756598477982859)
                    ·
                      rfl

theorem cell23_6811698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_6811698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811698 prefixEnd_6811698 := by exact prefixLift 6811698
  have htrace : WordTrace (prefixWord ++ tailWord_6811698) baseStart_6811698 baseEnd_6811698 := by
    simpa [prefixWord, tailWord_6811698, baseEnd_6811698] using wordTrace_append hprefix tailTrace_6811698
  have hstable : (prefixWord ++ tailWord_6811698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811698).length < 2 ^ (prefixWord ++ tailWord_6811698).sum := by decide
  have hdescent : baseEnd_6811698 < baseStart_6811698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811738 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3]
def baseStart_6811738 : Nat := 118140960795 + 6811738 * 2 ^ 59
def prefixEnd_6811738 : Nat := 4983230072969 + 3 ^ 40 * 6811738 * 2
def baseEnd_6811738 : Nat := 3497695686495975277448393

theorem tailTrace_6811738 : CollatzResearch.WordTrace tailWord_6811738 prefixEnd_6811738 3497695686495975277448393 := by
  unfold tailWord_6811738
  simp only [CollatzResearch.WordTrace]
  refine ⟨62111123849061013269076967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165629663597496035384205245 62111123849061013269076967)
  ·
    refine ⟨93166685773591519903615451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62111123849061013269076967 93166685773591519903615451)
    ·
      refine ⟨139750028660387279855423177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93166685773591519903615451 139750028660387279855423177)
      ·
        refine ⟨104812521495290459891567383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139750028660387279855423177 104812521495290459891567383)
        ·
          refine ⟨157218782242935689837351075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104812521495290459891567383 157218782242935689837351075)
          ·
            refine ⟨235828173364403534756026613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157218782242935689837351075 235828173364403534756026613)
            ·
              refine ⟨22108891252912831383377495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235828173364403534756026613 22108891252912831383377495)
              ·
                refine ⟨33163336879369247075066243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22108891252912831383377495 33163336879369247075066243)
                ·
                  refine ⟨49745005319053870612599365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33163336879369247075066243 49745005319053870612599365)
                  ·
                    refine ⟨9327188497322600739862381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49745005319053870612599365 9327188497322600739862381)
                    ·
                      refine ⟨3497695686495975277448393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9327188497322600739862381 3497695686495975277448393)
                      ·
                        rfl

theorem cell23_6811738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3].length) (baseStart_6811738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811738 prefixEnd_6811738 := by exact prefixLift 6811738
  have htrace : WordTrace (prefixWord ++ tailWord_6811738) baseStart_6811738 baseEnd_6811738 := by
    simpa [prefixWord, tailWord_6811738, baseEnd_6811738] using wordTrace_append hprefix tailTrace_6811738
  have hstable : (prefixWord ++ tailWord_6811738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811738).length < 2 ^ (prefixWord ++ tailWord_6811738).sum := by decide
  have hdescent : baseEnd_6811738 < baseStart_6811738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811758 : List Nat := [4, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_6811758 : Nat := 118140960795 + 6811758 * 2 ^ 59
def prefixEnd_6811758 : Nat := 4983230072969 + 3 ^ 40 * 6811758 * 2
def baseEnd_6811758 : Nat := 388633995123229466577589

theorem tailTrace_6811758 : CollatzResearch.WordTrace tailWord_6811758 prefixEnd_6811758 388633995123229466577589 := by
  unfold tailWord_6811758
  simp only [CollatzResearch.WordTrace]
  refine ⟨31055653107021449561504491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165630149904114397661357285 31055653107021449561504491)
  ·
    refine ⟨46583479660532174342256737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31055653107021449561504491 46583479660532174342256737)
    ·
      refine ⟨34937609745399130756692553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46583479660532174342256737 34937609745399130756692553)
      ·
        refine ⟨26203207309049348067519415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34937609745399130756692553 26203207309049348067519415)
        ·
          refine ⟨39304810963574022101279123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26203207309049348067519415 39304810963574022101279123)
          ·
            refine ⟨58957216445361033151918685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39304810963574022101279123 58957216445361033151918685)
            ·
              refine ⟨22108956167010387431969507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58957216445361033151918685 22108956167010387431969507)
              ·
                refine ⟨33163434250515581147954261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22108956167010387431969507 33163434250515581147954261)
                ·
                  refine ⟨388633995123229466577589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33163434250515581147954261 388633995123229466577589)
                  ·
                    rfl

theorem cell23_6811758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_6811758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811758 prefixEnd_6811758 := by exact prefixLift 6811758
  have htrace : WordTrace (prefixWord ++ tailWord_6811758) baseStart_6811758 baseEnd_6811758 := by
    simpa [prefixWord, tailWord_6811758, baseEnd_6811758] using wordTrace_append hprefix tailTrace_6811758
  have hstable : (prefixWord ++ tailWord_6811758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811758).length < 2 ^ (prefixWord ++ tailWord_6811758).sum := by decide
  have hdescent : baseEnd_6811758 < baseStart_6811758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811761 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_6811761 : Nat := 118140960795 + 6811761 * 2 ^ 59
def prefixEnd_6811761 : Nat := 4983230072969 + 3 ^ 40 * 6811761 * 2
def baseEnd_6811761 : Nat := 3497707496551028687460787

theorem tailTrace_6811761 : CollatzResearch.WordTrace tailWord_6811761 prefixEnd_6811761 3497707496551028687460787 := by
  unfold tailWord_6811761
  simp only [CollatzResearch.WordTrace]
  refine ⟨248445334275160728004395137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165630222850107152002930091 248445334275160728004395137)
  ·
    refine ⟨186334000706370546003296353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248445334275160728004395137 186334000706370546003296353)
    ·
      refine ⟨139750500529777909502472265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186334000706370546003296353 139750500529777909502472265)
      ·
        refine ⟨104812875397333432126854199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139750500529777909502472265 104812875397333432126854199)
        ·
          refine ⟨157219313096000148190281299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104812875397333432126854199 157219313096000148190281299)
          ·
            refine ⟨235828969644000222285421949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157219313096000148190281299 235828969644000222285421949)
            ·
              refine ⟨88435863616500083357033231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235828969644000222285421949 88435863616500083357033231)
              ·
                refine ⟨132653795424750125035549847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88435863616500083357033231 132653795424750125035549847)
                ·
                  refine ⟨198980693137125187553324771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132653795424750125035549847 198980693137125187553324771)
                  ·
                    refine ⟨298471039705687781329987157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 198980693137125187553324771 298471039705687781329987157)
                    ·
                      refine ⟨3497707496551028687460787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 298471039705687781329987157 3497707496551028687460787)
                      ·
                        rfl

theorem cell23_6811761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_6811761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811761 prefixEnd_6811761 := by exact prefixLift 6811761
  have htrace : WordTrace (prefixWord ++ tailWord_6811761) baseStart_6811761 baseEnd_6811761 := by
    simpa [prefixWord, tailWord_6811761, baseEnd_6811761] using wordTrace_append hprefix tailTrace_6811761
  have hstable : (prefixWord ++ tailWord_6811761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811761).length < 2 ^ (prefixWord ++ tailWord_6811761).sum := by decide
  have hdescent : baseEnd_6811761 < baseStart_6811761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811762 : List Nat := [3, 2, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_6811762 : Nat := 118140960795 + 6811762 * 2 ^ 59
def prefixEnd_6811762 : Nat := 4983230072969 + 3 ^ 40 * 6811762 * 2
def baseEnd_6811762 : Nat := 1165902670010561061182761

theorem tailTrace_6811762 : CollatzResearch.WordTrace tailWord_6811762 prefixEnd_6811762 1165902670010561061182761 := by
  unfold tailWord_6811762
  simp only [CollatzResearch.WordTrace]
  refine ⟨62111342687039276293795385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165630247165438070116787693 62111342687039276293795385)
  ·
    refine ⟨46583507015279457220346539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62111342687039276293795385 46583507015279457220346539)
    ·
      refine ⟨69875260522919185830519809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46583507015279457220346539 69875260522919185830519809)
      ·
        refine ⟨52406445392189389372889857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69875260522919185830519809 52406445392189389372889857)
        ·
          refine ⟨39304834044142042029667393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52406445392189389372889857 39304834044142042029667393)
          ·
            refine ⟨29478625533106531522250545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39304834044142042029667393 29478625533106531522250545)
            ·
              refine ⟨22108969149829898641687909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29478625533106531522250545 22108969149829898641687909)
              ·
                refine ⟨4145431715593105995316483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22108969149829898641687909 4145431715593105995316483)
                ·
                  refine ⟨6218147573389658992974725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145431715593105995316483 6218147573389658992974725)
                  ·
                    refine ⟨1165902670010561061182761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218147573389658992974725 1165902670010561061182761)
                    ·
                      rfl

theorem cell23_6811762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_6811762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811762 prefixEnd_6811762 := by exact prefixLift 6811762
  have htrace : WordTrace (prefixWord ++ tailWord_6811762) baseStart_6811762 baseEnd_6811762 := by
    simpa [prefixWord, tailWord_6811762, baseEnd_6811762] using wordTrace_append hprefix tailTrace_6811762
  have hstable : (prefixWord ++ tailWord_6811762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811762).length < 2 ^ (prefixWord ++ tailWord_6811762).sum := by decide
  have hdescent : baseEnd_6811762 < baseStart_6811762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811785 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 3]
def baseStart_6811785 : Nat := 118140960795 + 6811785 * 2 ^ 59
def prefixEnd_6811785 : Nat := 4983230072969 + 3 ^ 40 * 6811785 * 2
def baseEnd_6811785 : Nat := 3497719820086736593560677

theorem tailTrace_6811785 : CollatzResearch.WordTrace tailWord_6811785 prefixEnd_6811785 3497719820086736593560677 := by
  unfold tailWord_6811785
  simp only [CollatzResearch.WordTrace]
  refine ⟨248446209627073780103268809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165630806418049186735512539 248446209627073780103268809)
  ·
    refine ⟨186334657220305335077451607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248446209627073780103268809 186334657220305335077451607)
    ·
      refine ⟨279501985830458002616177411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186334657220305335077451607 279501985830458002616177411)
      ·
        refine ⟨419252978745687003924266117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279501985830458002616177411 419252978745687003924266117)
        ·
          refine ⟨78609933514816313235799897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419252978745687003924266117 78609933514816313235799897)
          ·
            refine ⟨58957450136112234926849923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78609933514816313235799897 58957450136112234926849923)
            ·
              refine ⟨88436175204168352390274885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58957450136112234926849923 88436175204168352390274885)
              ·
                refine ⟨16581782850781566073176541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88436175204168352390274885 16581782850781566073176541)
                ·
                  refine ⟨6218168569043087277441203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16581782850781566073176541 6218168569043087277441203)
                  ·
                    refine ⟨9327252853564630916161805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6218168569043087277441203 9327252853564630916161805)
                    ·
                      refine ⟨3497719820086736593560677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9327252853564630916161805 3497719820086736593560677)
                      ·
                        rfl

theorem cell23_6811785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_6811785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811785 prefixEnd_6811785 := by exact prefixLift 6811785
  have htrace : WordTrace (prefixWord ++ tailWord_6811785) baseStart_6811785 baseEnd_6811785 := by
    simpa [prefixWord, tailWord_6811785, baseEnd_6811785] using wordTrace_append hprefix tailTrace_6811785
  have hstable : (prefixWord ++ tailWord_6811785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811785).length < 2 ^ (prefixWord ++ tailWord_6811785).sum := by decide
  have hdescent : baseEnd_6811785 < baseStart_6811785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811795 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 2, 3, 2]
def baseStart_6811795 : Nat := 118140960795 + 6811795 * 2 ^ 59
def prefixEnd_6811795 : Nat := 4983230072969 + 3 ^ 40 * 6811795 * 2
def baseEnd_6811795 : Nat := 3497724954893281554435631

theorem tailTrace_6811795 : CollatzResearch.WordTrace tailWord_6811795 prefixEnd_6811795 3497724954893281554435631 := by
  unfold tailWord_6811795
  simp only [CollatzResearch.WordTrace]
  refine ⟨248446574357037551811132839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165631049571358367874088559 248446574357037551811132839)
  ·
    refine ⟨372669861535556327716699259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248446574357037551811132839 372669861535556327716699259)
    ·
      refine ⟨559004792303334491575048889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372669861535556327716699259 559004792303334491575048889)
      ·
        refine ⟨419253594227500868681286667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559004792303334491575048889 419253594227500868681286667)
        ·
          refine ⟨628880391341251303021930001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419253594227500868681286667 628880391341251303021930001)
          ·
            refine ⟨471660293505938477266447501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628880391341251303021930001 471660293505938477266447501)
            ·
              refine ⟨176872610064726928974917813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 471660293505938477266447501 176872610064726928974917813)
              ·
                refine ⟨16581807193568149591398545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176872610064726928974917813 16581807193568149591398545)
                ·
                  refine ⟨12436355395176112193548909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16581807193568149591398545 12436355395176112193548909)
                  ·
                    refine ⟨4663633273191042072580841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12436355395176112193548909 4663633273191042072580841)
                    ·
                      refine ⟨3497724954893281554435631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663633273191042072580841 3497724954893281554435631)
                      ·
                        rfl

theorem cell23_6811795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3, 2].length) (baseStart_6811795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811795 prefixEnd_6811795 := by exact prefixLift 6811795
  have htrace : WordTrace (prefixWord ++ tailWord_6811795) baseStart_6811795 baseEnd_6811795 := by
    simpa [prefixWord, tailWord_6811795, baseEnd_6811795] using wordTrace_append hprefix tailTrace_6811795
  have hstable : (prefixWord ++ tailWord_6811795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811795).length < 2 ^ (prefixWord ++ tailWord_6811795).sum := by decide
  have hdescent : baseEnd_6811795 < baseStart_6811795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811805 : List Nat := [1, 4, 2, 1, 1, 3, 2, 3, 1, 5]
def baseStart_6811805 : Nat := 118140960795 + 6811805 * 2 ^ 59
def prefixEnd_6811805 : Nat := 4983230072969 + 3 ^ 40 * 6811805 * 2
def baseEnd_6811805 : Nat := 1165910029899942171770195

theorem tailTrace_6811805 : CollatzResearch.WordTrace tailWord_6811805 prefixEnd_6811805 1165910029899942171770195 := by
  unfold tailWord_6811805
  simp only [CollatzResearch.WordTrace]
  refine ⟨248446939087001323518996869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165631292724667549012664579 248446939087001323518996869)
  ·
    refine ⟨46583801078812748159811913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248446939087001323518996869 46583801078812748159811913)
    ·
      refine ⟨34937850809109561119858935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46583801078812748159811913 34937850809109561119858935)
      ·
        refine ⟨52406776213664341679788403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34937850809109561119858935 52406776213664341679788403)
        ·
          refine ⟨78610164320496512519682605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52406776213664341679788403 78610164320496512519682605)
          ·
            refine ⟨29478811620186192194880977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78610164320496512519682605 29478811620186192194880977)
            ·
              refine ⟨22109108715139644146160733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29478811620186192194880977 22109108715139644146160733)
              ·
                refine ⟨8290915768177366554810275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22109108715139644146160733 8290915768177366554810275)
                ·
                  refine ⟨12436373652266049832215413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8290915768177366554810275 12436373652266049832215413)
                  ·
                    refine ⟨1165910029899942171770195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12436373652266049832215413 1165910029899942171770195)
                    ·
                      rfl

theorem cell23_6811805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_6811805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811805 prefixEnd_6811805 := by exact prefixLift 6811805
  have htrace : WordTrace (prefixWord ++ tailWord_6811805) baseStart_6811805 baseEnd_6811805 := by
    simpa [prefixWord, tailWord_6811805, baseEnd_6811805] using wordTrace_append hprefix tailTrace_6811805
  have hstable : (prefixWord ++ tailWord_6811805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811805).length < 2 ^ (prefixWord ++ tailWord_6811805).sum := by decide
  have hdescent : baseEnd_6811805 < baseStart_6811805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811835 : List Nat := [1, 1, 1, 1, 1, 2, 7, 3, 2, 4]
def baseStart_6811835 : Nat := 118140960795 + 6811835 * 2 ^ 59
def prefixEnd_6811835 : Nat := 4983230072969 + 3 ^ 40 * 6811835 * 2
def baseEnd_6811835 : Nat := 1165915164706487132645149

theorem tailTrace_6811835 : CollatzResearch.WordTrace tailWord_6811835 prefixEnd_6811835 1165915164706487132645149 := by
  unfold tailWord_6811835
  simp only [CollatzResearch.WordTrace]
  refine ⟨248448033276892638642588959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165632022184595092428392639 248448033276892638642588959)
  ·
    refine ⟨372672049915338957963883439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248448033276892638642588959 372672049915338957963883439)
    ·
      refine ⟨559008074873008436945825159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372672049915338957963883439 559008074873008436945825159)
      ·
        refine ⟨838512112309512655418737739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559008074873008436945825159 838512112309512655418737739)
        ·
          refine ⟨1257768168464268983128106609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838512112309512655418737739 1257768168464268983128106609)
          ·
            refine ⟨943326126348201737346079957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257768168464268983128106609 943326126348201737346079957)
            ·
              refine ⟨22109206086285978219048749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 943326126348201737346079957 22109206086285978219048749)
              ·
                refine ⟨8290952282357241832143281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22109206086285978219048749 8290952282357241832143281)
                ·
                  refine ⟨6218214211767931374107461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8290952282357241832143281 6218214211767931374107461)
                  ·
                    refine ⟨1165915164706487132645149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218214211767931374107461 1165915164706487132645149)
                    ·
                      rfl

theorem cell23_6811835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 4].length) (baseStart_6811835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811835 prefixEnd_6811835 := by exact prefixLift 6811835
  have htrace : WordTrace (prefixWord ++ tailWord_6811835) baseStart_6811835 baseEnd_6811835 := by
    simpa [prefixWord, tailWord_6811835, baseEnd_6811835] using wordTrace_append hprefix tailTrace_6811835
  have hstable : (prefixWord ++ tailWord_6811835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811835).length < 2 ^ (prefixWord ++ tailWord_6811835).sum := by decide
  have hdescent : baseEnd_6811835 < baseStart_6811835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811852 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 1, 6]
def baseStart_6811852 : Nat := 118140960795 + 6811852 * 2 ^ 59
def prefixEnd_6811852 : Nat := 4983230072969 + 3 ^ 40 * 6811852 * 2
def baseEnd_6811852 : Nat := 1165918074430195943807623

theorem tailTrace_6811852 : CollatzResearch.WordTrace tailWord_6811852 prefixEnd_6811852 1165918074430195943807623 := by
  unfold tailWord_6811852
  simp only [CollatzResearch.WordTrace]
  refine ⟨124224326658915525272978905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165632435545220700363971873 124224326658915525272978905)
  ·
    refine ⟨93168244994186643954734179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124224326658915525272978905 93168244994186643954734179)
    ·
      refine ⟨139752367491279965932101269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93168244994186643954734179 139752367491279965932101269)
      ·
        refine ⟨6550892226153748403067247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139752367491279965932101269 6550892226153748403067247)
        ·
          refine ⟨9826338339230622604600871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6550892226153748403067247 9826338339230622604600871)
          ·
            refine ⟨14739507508845933906901307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9826338339230622604600871 14739507508845933906901307)
            ·
              refine ⟨22109261263268900860351961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14739507508845933906901307 22109261263268900860351961)
              ·
                refine ⟨16581945947451675645263971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22109261263268900860351961 16581945947451675645263971)
                ·
                  refine ⟨24872918921177513467895957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16581945947451675645263971 24872918921177513467895957)
                  ·
                    refine ⟨1165918074430195943807623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24872918921177513467895957 1165918074430195943807623)
                    ·
                      rfl

theorem cell23_6811852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 1, 6].length) (baseStart_6811852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811852 prefixEnd_6811852 := by exact prefixLift 6811852
  have htrace : WordTrace (prefixWord ++ tailWord_6811852) baseStart_6811852 baseEnd_6811852 := by
    simpa [prefixWord, tailWord_6811852, baseEnd_6811852] using wordTrace_append hprefix tailTrace_6811852
  have hstable : (prefixWord ++ tailWord_6811852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811852).length < 2 ^ (prefixWord ++ tailWord_6811852).sum := by decide
  have hdescent : baseEnd_6811852 < baseStart_6811852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811869 : List Nat := [1, 4, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_6811869 : Nat := 118140960795 + 6811869 * 2 ^ 59
def prefixEnd_6811869 : Nat := 4983230072969 + 3 ^ 40 * 6811869 * 2
def baseEnd_6811869 : Nat := 1165920984153904754970097

theorem tailTrace_6811869 : CollatzResearch.WordTrace tailWord_6811869 prefixEnd_6811869 1165920984153904754970097 := by
  unfold tailWord_6811869
  simp only [CollatzResearch.WordTrace]
  refine ⟨248449273358769462449326661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165632848905846308299551107 248449273358769462449326661)
  ·
    refine ⟨46584238754769274209248749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248449273358769462449326661 46584238754769274209248749)
    ·
      refine ⟨17469089533038477828468281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46584238754769274209248749 17469089533038477828468281)
      ·
        refine ⟨13101817149778858371351211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17469089533038477828468281 13101817149778858371351211)
        ·
          refine ⟨19652725724668287557026817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13101817149778858371351211 19652725724668287557026817)
          ·
            refine ⟨14739544293501215667770113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19652725724668287557026817 14739544293501215667770113)
            ·
              refine ⟨11054658220125911750827585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14739544293501215667770113 11054658220125911750827585)
              ·
                refine ⟨8290993665094433813120689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11054658220125911750827585 8290993665094433813120689)
                ·
                  refine ⟨6218245248820825359840517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8290993665094433813120689 6218245248820825359840517)
                  ·
                    refine ⟨1165920984153904754970097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218245248820825359840517 1165920984153904754970097)
                    ·
                      rfl

theorem cell23_6811869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_6811869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811869 prefixEnd_6811869 := by exact prefixLift 6811869
  have htrace : WordTrace (prefixWord ++ tailWord_6811869) baseStart_6811869 baseEnd_6811869 := by
    simpa [prefixWord, tailWord_6811869, baseEnd_6811869] using wordTrace_append hprefix tailTrace_6811869
  have hstable : (prefixWord ++ tailWord_6811869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811869).length < 2 ^ (prefixWord ++ tailWord_6811869).sum := by decide
  have hdescent : baseEnd_6811869 < baseStart_6811869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811943 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6811943 : Nat := 118140960795 + 6811943 * 2 ^ 59
def prefixEnd_6811943 : Nat := 4983230072969 + 3 ^ 40 * 6811943 * 2
def baseEnd_6811943 : Nat := 3497800950030146975384951

theorem tailTrace_6811943 : CollatzResearch.WordTrace tailWord_6811943 prefixEnd_6811943 3497800950030146975384951 := by
  unfold tailWord_6811943
  simp only [CollatzResearch.WordTrace]
  refine ⟨248451972360501373087520483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165634648240334248725013655 248451972360501373087520483)
  ·
    refine ⟨372677958540752059631280725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248451972360501373087520483 372677958540752059631280725)
    ·
      refine ⟨4367319826649438198804071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 372677958540752059631280725 4367319826649438198804071)
      ·
        refine ⟨6550979739974157298206107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367319826649438198804071 6550979739974157298206107)
        ·
          refine ⟨9826469609961235947309161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6550979739974157298206107 9826469609961235947309161)
          ·
            refine ⟨7369852207470926960481871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9826469609961235947309161 7369852207470926960481871)
            ·
              refine ⟨11054778311206390440722807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369852207470926960481871 11054778311206390440722807)
              ·
                refine ⟨16582167466809585661084211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054778311206390440722807 16582167466809585661084211)
                ·
                  refine ⟨24873251200214378491626317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16582167466809585661084211 24873251200214378491626317)
                  ·
                    refine ⟨9327469200080391934359869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24873251200214378491626317 9327469200080391934359869)
                    ·
                      refine ⟨3497800950030146975384951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9327469200080391934359869 3497800950030146975384951)
                      ·
                        rfl

theorem cell23_6811943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6811943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811943 prefixEnd_6811943 := by exact prefixLift 6811943
  have htrace : WordTrace (prefixWord ++ tailWord_6811943) baseStart_6811943 baseEnd_6811943 := by
    simpa [prefixWord, tailWord_6811943, baseEnd_6811943] using wordTrace_append hprefix tailTrace_6811943
  have hstable : (prefixWord ++ tailWord_6811943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811943).length < 2 ^ (prefixWord ++ tailWord_6811943).sum := by decide
  have hdescent : baseEnd_6811943 < baseStart_6811943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811985 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 4, 5]
def baseStart_6811985 : Nat := 118140960795 + 6811985 * 2 ^ 59
def prefixEnd_6811985 : Nat := 4983230072969 + 3 ^ 40 * 6811985 * 2
def baseEnd_6811985 : Nat := 1165940838739211937019919

theorem tailTrace_6811985 : CollatzResearch.WordTrace tailWord_6811985 prefixEnd_6811985 1165940838739211937019919 := by
  unfold tailWord_6811985
  simp only [CollatzResearch.WordTrace]
  refine ⟨248453504226349214260549409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165635669484232809507032939 248453504226349214260549409)
  ·
    refine ⟨186340128169761910695412057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248453504226349214260549409 186340128169761910695412057)
    ·
      refine ⟨139755096127321433021559043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186340128169761910695412057 139755096127321433021559043)
      ·
        refine ⟨209632644190982149532338565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139755096127321433021559043 209632644190982149532338565)
        ·
          refine ⟨39306120785809153037313481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209632644190982149532338565 39306120785809153037313481)
          ·
            refine ⟨29479590589356864777985111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39306120785809153037313481 29479590589356864777985111)
            ·
              refine ⟨44219385884035297166977667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29479590589356864777985111 44219385884035297166977667)
              ·
                refine ⟨66329078826052945750466501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44219385884035297166977667 66329078826052945750466501)
                ·
                  refine ⟨12436702279884927328212469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66329078826052945750466501 12436702279884927328212469)
                  ·
                    refine ⟨1165940838739211937019919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12436702279884927328212469 1165940838739211937019919)
                    ·
                      rfl

theorem cell23_6811985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_6811985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811985 prefixEnd_6811985 := by exact prefixLift 6811985
  have htrace : WordTrace (prefixWord ++ tailWord_6811985) baseStart_6811985 baseEnd_6811985 := by
    simpa [prefixWord, tailWord_6811985, baseEnd_6811985] using wordTrace_append hprefix tailTrace_6811985
  have hstable : (prefixWord ++ tailWord_6811985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811985).length < 2 ^ (prefixWord ++ tailWord_6811985).sum := by decide
  have hdescent : baseEnd_6811985 < baseStart_6811985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6811989 : List Nat := [1, 3, 2, 2, 5, 1, 1, 1, 7]
def baseStart_6811989 : Nat := 118140960795 + 6811989 * 2 ^ 59
def prefixEnd_6811989 : Nat := 4983230072969 + 3 ^ 40 * 6811989 * 2
def baseEnd_6811989 : Nat := 388647174460028199489971

theorem tailTrace_6811989 : CollatzResearch.WordTrace tailWord_6811989 prefixEnd_6811989 388647174460028199489971 := by
  unfold tailWord_6811989
  simp only [CollatzResearch.WordTrace]
  refine ⟨248453650118334722943695021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165635766745556481962463347 248453650118334722943695021)
  ·
    refine ⟨93170118794375521103885633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248453650118334722943695021 93170118794375521103885633)
    ·
      refine ⟨69877589095781640827914225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93170118794375521103885633 69877589095781640827914225)
      ·
        refine ⟨52408191821836230620935669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69877589095781640827914225 52408191821836230620935669)
        ·
          refine ⟨4913267983297146620712719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52408191821836230620935669 4913267983297146620712719)
          ·
            refine ⟨7369901974945719931069079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913267983297146620712719 7369901974945719931069079)
            ·
              refine ⟨11054852962418579896603619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7369901974945719931069079 11054852962418579896603619)
              ·
                refine ⟨16582279443627869844905429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11054852962418579896603619 16582279443627869844905429)
                ·
                  refine ⟨388647174460028199489971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16582279443627869844905429 388647174460028199489971)
                  ·
                    rfl

theorem cell23_6811989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 7].length) (baseStart_6811989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6811989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6811989 prefixEnd_6811989 := by exact prefixLift 6811989
  have htrace : WordTrace (prefixWord ++ tailWord_6811989) baseStart_6811989 baseEnd_6811989 := by
    simpa [prefixWord, tailWord_6811989, baseEnd_6811989] using wordTrace_append hprefix tailTrace_6811989
  have hstable : (prefixWord ++ tailWord_6811989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6811989).length < 2 ^ (prefixWord ++ tailWord_6811989).sum := by decide
  have hdescent : baseEnd_6811989 < baseStart_6811989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6811989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812000 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 2, 2, 2]
def baseStart_6812000 : Nat := 118140960795 + 6812000 * 2 ^ 59
def prefixEnd_6812000 : Nat := 4983230072969 + 3 ^ 40 * 6812000 * 2
def baseEnd_6812000 : Nat := 3497830218427453252372189

theorem tailTrace_6812000 : CollatzResearch.WordTrace tailWord_6812000 prefixEnd_6812000 3497830218427453252372189 := by
  unfold tailWord_6812000
  simp only [CollatzResearch.WordTrace]
  refine ⟨124227025660647435911172727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165636034214196581214896969 124227025660647435911172727)
  ·
    refine ⟨186340538490971153866759091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124227025660647435911172727 186340538490971153866759091)
    ·
      refine ⟨279510807736456730800138637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186340538490971153866759091 279510807736456730800138637)
      ·
        refine ⟨104816552901171274050051989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279510807736456730800138637 104816552901171274050051989)
        ·
          refine ⟨4913275917242403471096187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104816552901171274050051989 4913275917242403471096187)
          ·
            refine ⟨7369913875863605206644281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913275917242403471096187 7369913875863605206644281)
            ·
              refine ⟨5527435406897703904983211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7369913875863605206644281 5527435406897703904983211)
              ·
                refine ⟨8291153110346555857474817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527435406897703904983211 8291153110346555857474817)
                ·
                  refine ⟨6218364832759916893106113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8291153110346555857474817 6218364832759916893106113)
                  ·
                    refine ⟨4663773624569937669829585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218364832759916893106113 4663773624569937669829585)
                    ·
                      refine ⟨3497830218427453252372189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663773624569937669829585 3497830218427453252372189)
                      ·
                        rfl

theorem cell23_6812000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_6812000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812000 prefixEnd_6812000 := by exact prefixLift 6812000
  have htrace : WordTrace (prefixWord ++ tailWord_6812000) baseStart_6812000 baseEnd_6812000 := by
    simpa [prefixWord, tailWord_6812000, baseEnd_6812000] using wordTrace_append hprefix tailTrace_6812000
  have hstable : (prefixWord ++ tailWord_6812000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812000).length < 2 ^ (prefixWord ++ tailWord_6812000).sum := by decide
  have hdescent : baseEnd_6812000 < baseStart_6812000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812105 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 3, 6]
def baseStart_6812105 : Nat := 118140960795 + 6812105 * 2 ^ 59
def prefixEnd_6812105 : Nat := 4983230072969 + 3 ^ 40 * 6812105 * 2
def baseEnd_6812105 : Nat := 1165961377965391780519735

theorem tailTrace_6812105 : CollatzResearch.WordTrace tailWord_6812105 prefixEnd_6812105 1165961377965391780519735 := by
  unfold tailWord_6812105
  simp only [CollatzResearch.WordTrace]
  refine ⟨248457880985914474754917769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165638587323942983169945179 248457880985914474754917769)
  ·
    refine ⟨186343410739435856066188327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248457880985914474754917769 186343410739435856066188327)
    ·
      refine ⟨279515116109153784099282491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186343410739435856066188327 279515116109153784099282491)
      ·
        refine ⟨419272674163730676148923737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279515116109153784099282491 419272674163730676148923737)
        ·
          refine ⟨314454505622798007111692803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419272674163730676148923737 314454505622798007111692803)
          ·
            refine ⟨471681758434197010667539205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314454505622798007111692803 471681758434197010667539205)
            ·
              refine ⟨88440329706411939500163601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 471681758434197010667539205 88440329706411939500163601)
              ·
                refine ⟨66330247279808954625122701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88440329706411939500163601 66330247279808954625122701)
                ·
                  refine ⟨24873842729928357984421013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66330247279808954625122701 24873842729928357984421013)
                  ·
                    refine ⟨1165961377965391780519735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24873842729928357984421013 1165961377965391780519735)
                    ·
                      rfl

theorem cell23_6812105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_6812105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812105 prefixEnd_6812105 := by exact prefixLift 6812105
  have htrace : WordTrace (prefixWord ++ tailWord_6812105) baseStart_6812105 baseEnd_6812105 := by
    simpa [prefixWord, tailWord_6812105, baseEnd_6812105] using wordTrace_append hprefix tailTrace_6812105
  have hstable : (prefixWord ++ tailWord_6812105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812105).length < 2 ^ (prefixWord ++ tailWord_6812105).sum := by decide
  have hdescent : baseEnd_6812105 < baseStart_6812105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812106 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3]
def baseStart_6812106 : Nat := 118140960795 + 6812106 * 2 ^ 59
def prefixEnd_6812106 : Nat := 4983230072969 + 3 ^ 40 * 6812106 * 2
def baseEnd_6812106 : Nat := 3497884647376829837646701

theorem tailTrace_6812106 : CollatzResearch.WordTrace tailWord_6812106 prefixEnd_6812106 3497884647376829837646701 := by
  unfold tailWord_6812106
  simp only [CollatzResearch.WordTrace]
  refine ⟨62114479364727712981426043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165638611639273901283802781 62114479364727712981426043)
  ·
    refine ⟨93171719047091569472139065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62114479364727712981426043 93171719047091569472139065)
    ·
      refine ⟨69878789285318677104104299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93171719047091569472139065 69878789285318677104104299)
      ·
        refine ⟨104818183927978015656156449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69878789285318677104104299 104818183927978015656156449)
        ·
          refine ⟨78613637945983511742117337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104818183927978015656156449 78613637945983511742117337)
          ·
            refine ⟨58960228459487633806588003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78613637945983511742117337 58960228459487633806588003)
            ·
              refine ⟨88440342689231450709882005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58960228459487633806588003 88440342689231450709882005)
              ·
                refine ⟨4145641063557724252025719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88440342689231450709882005 4145641063557724252025719)
                ·
                  refine ⟨6218461595336586378038579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145641063557724252025719 6218461595336586378038579)
                  ·
                    refine ⟨9327692393004879567057869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6218461595336586378038579 9327692393004879567057869)
                    ·
                      refine ⟨3497884647376829837646701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9327692393004879567057869 3497884647376829837646701)
                      ·
                        rfl

theorem cell23_6812106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3].length) (baseStart_6812106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812106 prefixEnd_6812106 := by exact prefixLift 6812106
  have htrace : WordTrace (prefixWord ++ tailWord_6812106) baseStart_6812106 baseEnd_6812106 := by
    simpa [prefixWord, tailWord_6812106, baseEnd_6812106] using wordTrace_append hprefix tailTrace_6812106
  have hstable : (prefixWord ++ tailWord_6812106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812106).length < 2 ^ (prefixWord ++ tailWord_6812106).sum := by decide
  have hdescent : baseEnd_6812106 < baseStart_6812106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812112 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 6, 2]
def baseStart_6812112 : Nat := 118140960795 + 6812112 * 2 ^ 59
def prefixEnd_6812112 : Nat := 4983230072969 + 3 ^ 40 * 6812112 * 2
def baseEnd_6812112 : Nat := 3497887728260756814171673

theorem tailTrace_6812112 : CollatzResearch.WordTrace tailWord_6812112 prefixEnd_6812112 3497887728260756814171673 := by
  unfold tailWord_6812112
  simp only [CollatzResearch.WordTrace]
  refine ⟨124229068148444557475211295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165638757531259409966948393 124229068148444557475211295)
  ·
    refine ⟨186343602222666836212816943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124229068148444557475211295 186343602222666836212816943)
    ·
      refine ⟨279515403334000254319225415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186343602222666836212816943 279515403334000254319225415)
      ·
        refine ⟨419273105001000381478838123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279515403334000254319225415 419273105001000381478838123)
        ·
          refine ⟨628909657501500572218257185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419273105001000381478838123 628909657501500572218257185)
          ·
            refine ⟨471682243126125429163692889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628909657501500572218257185 471682243126125429163692889)
            ·
              refine ⟨353761682344594071872769667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471682243126125429163692889 353761682344594071872769667)
              ·
                refine ⟨530642523516891107809154501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353761682344594071872769667 530642523516891107809154501)
                ·
                  refine ⟨99495473159417082714216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530642523516891107809154501 99495473159417082714216469)
                  ·
                    refine ⟨4663850304347675752228897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99495473159417082714216469 4663850304347675752228897)
                    ·
                      refine ⟨3497887728260756814171673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663850304347675752228897 3497887728260756814171673)
                      ·
                        rfl

theorem cell23_6812112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 6, 2].length) (baseStart_6812112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812112 prefixEnd_6812112 := by exact prefixLift 6812112
  have htrace : WordTrace (prefixWord ++ tailWord_6812112) baseStart_6812112 baseEnd_6812112 := by
    simpa [prefixWord, tailWord_6812112, baseEnd_6812112] using wordTrace_append hprefix tailTrace_6812112
  have hstable : (prefixWord ++ tailWord_6812112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812112).length < 2 ^ (prefixWord ++ tailWord_6812112).sum := by decide
  have hdescent : baseEnd_6812112 < baseStart_6812112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812129 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_6812129 : Nat := 118140960795 + 6812129 * 2 ^ 59
def prefixEnd_6812129 : Nat := 4983230072969 + 3 ^ 40 * 6812129 * 2
def baseEnd_6812129 : Nat := 3497896457431883247659095

theorem tailTrace_6812129 : CollatzResearch.WordTrace tailWord_6812129 prefixEnd_6812129 3497896457431883247659095 := by
  unfold tailWord_6812129
  simp only [CollatzResearch.WordTrace]
  refine ⟨248458756337827526853791441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165639170891885017902527627 248458756337827526853791441)
  ·
    refine ⟨186344067253370645140343581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248458756337827526853791441 186344067253370645140343581)
    ·
      refine ⟨69879025220013991927628843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186344067253370645140343581 69879025220013991927628843)
      ·
        refine ⟨104818537830020987891443265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69879025220013991927628843 104818537830020987891443265)
        ·
          refine ⟨78613903372515740918582449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104818537830020987891443265 78613903372515740918582449)
          ·
            refine ⟨58960427529386805688936837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78613903372515740918582449 58960427529386805688936837)
            ·
              refine ⟨11055080161760026066675657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58960427529386805688936837 11055080161760026066675657)
              ·
                refine ⟨8291310121320019550006743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11055080161760026066675657 8291310121320019550006743)
                ·
                  refine ⟨12436965181980029325010115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8291310121320019550006743 12436965181980029325010115)
                  ·
                    refine ⟨18655447772970043987515173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12436965181980029325010115 18655447772970043987515173)
                    ·
                      refine ⟨3497896457431883247659095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18655447772970043987515173 3497896457431883247659095)
                      ·
                        rfl

theorem cell23_6812129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_6812129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812129 prefixEnd_6812129 := by exact prefixLift 6812129
  have htrace : WordTrace (prefixWord ++ tailWord_6812129) baseStart_6812129 baseEnd_6812129 := by
    simpa [prefixWord, tailWord_6812129, baseEnd_6812129] using wordTrace_append hprefix tailTrace_6812129
  have hstable : (prefixWord ++ tailWord_6812129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812129).length < 2 ^ (prefixWord ++ tailWord_6812129).sum := by decide
  have hdescent : baseEnd_6812129 < baseStart_6812129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812155 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_6812155 : Nat := 118140960795 + 6812155 * 2 ^ 59
def prefixEnd_6812155 : Nat := 4983230072969 + 3 ^ 40 * 6812155 * 2
def baseEnd_6812155 : Nat := 3497909807928900145933975

theorem tailTrace_6812155 : CollatzResearch.WordTrace tailWord_6812155 prefixEnd_6812155 3497909807928900145933975 := by
  unfold tailWord_6812155
  simp only [CollatzResearch.WordTrace]
  refine ⟨248459704635733333294237919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165639803090488888862825279 248459704635733333294237919)
  ·
    refine ⟨372689556953599999941356879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248459704635733333294237919 372689556953599999941356879)
    ·
      refine ⟨559034335430399999912035319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372689556953599999941356879 559034335430399999912035319)
      ·
        refine ⟨838551503145599999868052979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559034335430399999912035319 838551503145599999868052979)
        ·
          refine ⟨1257827254718399999802079469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838551503145599999868052979 1257827254718399999802079469)
          ·
            refine ⟨471685220519399999925779801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1257827254718399999802079469 471685220519399999925779801)
            ·
              refine ⟨353763915389549999944334851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471685220519399999925779801 353763915389549999944334851)
              ·
                refine ⟨530645873084324999916502277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353763915389549999944334851 530645873084324999916502277)
                ·
                  refine ⟨99496101203310937484344177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 530645873084324999916502277 99496101203310937484344177)
                  ·
                    refine ⟨74622075902483203113258133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99496101203310937484344177 74622075902483203113258133)
                    ·
                      refine ⟨3497909807928900145933975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74622075902483203113258133 3497909807928900145933975)
                      ·
                        rfl

theorem cell23_6812155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_6812155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812155 prefixEnd_6812155 := by exact prefixLift 6812155
  have htrace : WordTrace (prefixWord ++ tailWord_6812155) baseStart_6812155 baseEnd_6812155 := by
    simpa [prefixWord, tailWord_6812155, baseEnd_6812155] using wordTrace_append hprefix tailTrace_6812155
  have hstable : (prefixWord ++ tailWord_6812155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812155).length < 2 ^ (prefixWord ++ tailWord_6812155).sum := by decide
  have hdescent : baseEnd_6812155 < baseStart_6812155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812214 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2]
def baseStart_6812214 : Nat := 118140960795 + 6812214 * 2 ^ 59
def prefixEnd_6812214 : Nat := 4983230072969 + 3 ^ 40 * 6812214 * 2
def baseEnd_6812214 : Nat := 3497940103287515415096205

theorem tailTrace_6812214 : CollatzResearch.WordTrace tailWord_6812214 prefixEnd_6812214 3497940103287515415096205 := by
  unfold tailWord_6812214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15528866033907474148164731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165641237695013057580423797 15528866033907474148164731)
  ·
    refine ⟨23293299050861211222247097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15528866033907474148164731 23293299050861211222247097)
    ·
      refine ⟨17469974288145908416685323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23293299050861211222247097 17469974288145908416685323)
      ·
        refine ⟨26204961432218862625027985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17469974288145908416685323 26204961432218862625027985)
        ·
          refine ⟨19653721074164146968770989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26204961432218862625027985 19653721074164146968770989)
          ·
            refine ⟨7370145402811555113289121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19653721074164146968770989 7370145402811555113289121)
            ·
              refine ⟨5527609052108666334966841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7370145402811555113289121 5527609052108666334966841)
              ·
                refine ⟨4145706789081499751225131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5527609052108666334966841 4145706789081499751225131)
                ·
                  refine ⟨6218560183622249626837697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145706789081499751225131 6218560183622249626837697)
                  ·
                    refine ⟨4663920137716687220128273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218560183622249626837697 4663920137716687220128273)
                    ·
                      refine ⟨3497940103287515415096205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663920137716687220128273 3497940103287515415096205)
                      ·
                        rfl

theorem cell23_6812214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_6812214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812214 prefixEnd_6812214 := by exact prefixLift 6812214
  have htrace : WordTrace (prefixWord ++ tailWord_6812214) baseStart_6812214 baseEnd_6812214 := by
    simpa [prefixWord, tailWord_6812214, baseEnd_6812214] using wordTrace_append hprefix tailTrace_6812214
  have hstable : (prefixWord ++ tailWord_6812214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812214).length < 2 ^ (prefixWord ++ tailWord_6812214).sum := by decide
  have hdescent : baseEnd_6812214 < baseStart_6812214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812230 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_6812230 : Nat := 118140960795 + 6812230 * 2 ^ 59
def prefixEnd_6812230 : Nat := 4983230072969 + 3 ^ 40 * 6812230 * 2
def baseEnd_6812230 : Nat := 3497948318977987352496131

theorem tailTrace_6812230 : CollatzResearch.WordTrace tailWord_6812230 prefixEnd_6812230 3497948318977987352496131 := by
  unfold tailWord_6812230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7764451253451925659475567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165641626740307747402145429 7764451253451925659475567)
  ·
    refine ⟨11646676880177888489213351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7764451253451925659475567 11646676880177888489213351)
    ·
      refine ⟨17470015320266832733820027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11646676880177888489213351 17470015320266832733820027)
      ·
        refine ⟨26205022980400249100730041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17470015320266832733820027 26205022980400249100730041)
        ·
          refine ⟨19653767235300186825547531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26205022980400249100730041 19653767235300186825547531)
          ·
            refine ⟨29480650852950280238321297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19653767235300186825547531 29480650852950280238321297)
            ·
              refine ⟨22110488139712710178740973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29480650852950280238321297 22110488139712710178740973)
              ·
                refine ⟨8291433052392266317027865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22110488139712710178740973 8291433052392266317027865)
                ·
                  refine ⟨6218574789294199737770899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8291433052392266317027865 6218574789294199737770899)
                  ·
                    refine ⟨9327862183941299606656349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6218574789294199737770899 9327862183941299606656349)
                    ·
                      refine ⟨3497948318977987352496131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9327862183941299606656349 3497948318977987352496131)
                      ·
                        rfl

theorem cell23_6812230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_6812230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812230 prefixEnd_6812230 := by exact prefixLift 6812230
  have htrace : WordTrace (prefixWord ++ tailWord_6812230) baseStart_6812230 baseEnd_6812230 := by
    simpa [prefixWord, tailWord_6812230, baseEnd_6812230] using wordTrace_append hprefix tailTrace_6812230
  have hstable : (prefixWord ++ tailWord_6812230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812230).length < 2 ^ (prefixWord ++ tailWord_6812230).sum := by decide
  have hdescent : baseEnd_6812230 < baseStart_6812230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812236 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 1, 4, 2]
def baseStart_6812236 : Nat := 118140960795 + 6812236 * 2 ^ 59
def prefixEnd_6812236 : Nat := 4983230072969 + 3 ^ 40 * 6812236 * 2
def baseEnd_6812236 : Nat := 3497951399861914329021103

theorem tailTrace_6812236 : CollatzResearch.WordTrace tailWord_6812236 prefixEnd_6812236 3497951399861914329021103 := by
  unfold tailWord_6812236
  simp only [CollatzResearch.WordTrace]
  refine ⟨124231329474219942063968281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165641772632293256085291041 124231329474219942063968281)
  ·
    refine ⟨93173497105664956547976211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124231329474219942063968281 93173497105664956547976211)
    ·
      refine ⟨139760245658497434821964317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93173497105664956547976211 139760245658497434821964317)
      ·
        refine ⟨52410092121936538058236619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139760245658497434821964317 52410092121936538058236619)
        ·
          refine ⟨78615138182904807087354929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52410092121936538058236619 78615138182904807087354929)
          ·
            refine ⟨58961353637178605315516197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78615138182904807087354929 58961353637178605315516197)
            ·
              refine ⟨11055253806970988496659287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58961353637178605315516197 11055253806970988496659287)
              ·
                refine ⟨16582880710456482744988931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11055253806970988496659287 16582880710456482744988931)
                ·
                  refine ⟨24874321065684724117483397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16582880710456482744988931 24874321065684724117483397)
                  ·
                    refine ⟨4663935199815885772028137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24874321065684724117483397 4663935199815885772028137)
                    ·
                      refine ⟨3497951399861914329021103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663935199815885772028137 3497951399861914329021103)
                      ·
                        rfl

theorem cell23_6812236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_6812236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812236 prefixEnd_6812236 := by exact prefixLift 6812236
  have htrace : WordTrace (prefixWord ++ tailWord_6812236) baseStart_6812236 baseEnd_6812236 := by
    simpa [prefixWord, tailWord_6812236, baseEnd_6812236] using wordTrace_append hprefix tailTrace_6812236
  have hstable : (prefixWord ++ tailWord_6812236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812236).length < 2 ^ (prefixWord ++ tailWord_6812236).sum := by decide
  have hdescent : baseEnd_6812236 < baseStart_6812236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812270 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_6812270 : Nat := 118140960795 + 6812270 * 2 ^ 59
def prefixEnd_6812270 : Nat := 4983230072969 + 3 ^ 40 * 6812270 * 2
def baseEnd_6812270 : Nat := 3497968858204167195995947

theorem tailTrace_6812270 : CollatzResearch.WordTrace tailWord_6812270 prefixEnd_6812270 3497968858204167195995947 := by
  unfold tailWord_6812270
  simp only [CollatzResearch.WordTrace]
  refine ⟨31057987378789588491834283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165642599353544471956449509 31057987378789588491834283)
  ·
    refine ⟨46586981068184382737751425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31057987378789588491834283 46586981068184382737751425)
    ·
      refine ⟨34940235801138287053313569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46586981068184382737751425 34940235801138287053313569)
      ·
        refine ⟨26205176850853715289985177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34940235801138287053313569 26205176850853715289985177)
        ·
          refine ⟨19653882638140286467488883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26205176850853715289985177 19653882638140286467488883)
          ·
            refine ⟨29480823957210429701233325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19653882638140286467488883 29480823957210429701233325)
            ·
              refine ⟨11055308983953911137962497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29480823957210429701233325 11055308983953911137962497)
              ·
                refine ⟨8291481737965433353471873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11055308983953911137962497 8291481737965433353471873)
                ·
                  refine ⟨6218611303474075015103905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8291481737965433353471873 6218611303474075015103905)
                  ·
                    refine ⟨4663958477605556261327929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218611303474075015103905 4663958477605556261327929)
                    ·
                      refine ⟨3497968858204167195995947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663958477605556261327929 3497968858204167195995947)
                      ·
                        rfl

theorem cell23_6812270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_6812270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812270 prefixEnd_6812270 := by exact prefixLift 6812270
  have htrace : WordTrace (prefixWord ++ tailWord_6812270) baseStart_6812270 baseEnd_6812270 := by
    simpa [prefixWord, tailWord_6812270, baseEnd_6812270] using wordTrace_append hprefix tailTrace_6812270
  have hstable : (prefixWord ++ tailWord_6812270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812270).length < 2 ^ (prefixWord ++ tailWord_6812270).sum := by decide
  have hdescent : baseEnd_6812270 < baseStart_6812270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812279 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 7, 2]
def baseStart_6812279 : Nat := 118140960795 + 6812279 * 2 ^ 59
def prefixEnd_6812279 : Nat := 4983230072969 + 3 ^ 40 * 6812279 * 2
def baseEnd_6812279 : Nat := 3497973479530057660783405

theorem tailTrace_6812279 : CollatzResearch.WordTrace tailWord_6812279 prefixEnd_6812279 3497973479530057660783405 := by
  unfold tailWord_6812279
  simp only [CollatzResearch.WordTrace]
  refine ⟨248464227287284102471751891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165642818191522734981167927 248464227287284102471751891)
  ·
    refine ⟨372696340930926153707627837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248464227287284102471751891 372696340930926153707627837)
    ·
      refine ⟨139761127849097307640360439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372696340930926153707627837 139761127849097307640360439)
      ·
        refine ⟨209641691773645961460540659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139761127849097307640360439 209641691773645961460540659)
        ·
          refine ⟨314462537660468942190810989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209641691773645961460540659 314462537660468942190810989)
          ·
            refine ⟨117923451622675853321554121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314462537660468942190810989 117923451622675853321554121)
            ·
              refine ⟨88442588717006889991165591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117923451622675853321554121 88442588717006889991165591)
              ·
                refine ⟨132663883075510334986748387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88442588717006889991165591 132663883075510334986748387)
                ·
                  refine ⟨198995824613265502480122581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132663883075510334986748387 198995824613265502480122581)
                  ·
                    refine ⟨4663964639373410214377873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 198995824613265502480122581 4663964639373410214377873)
                    ·
                      refine ⟨3497973479530057660783405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4663964639373410214377873 3497973479530057660783405)
                      ·
                        rfl

theorem cell23_6812279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7, 2].length) (baseStart_6812279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812279 prefixEnd_6812279 := by exact prefixLift 6812279
  have htrace : WordTrace (prefixWord ++ tailWord_6812279) baseStart_6812279 baseEnd_6812279 := by
    simpa [prefixWord, tailWord_6812279, baseEnd_6812279] using wordTrace_append hprefix tailTrace_6812279
  have hstable : (prefixWord ++ tailWord_6812279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812279).length < 2 ^ (prefixWord ++ tailWord_6812279).sum := by decide
  have hdescent : baseEnd_6812279 < baseStart_6812279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812282 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_6812282 : Nat := 118140960795 + 6812282 * 2 ^ 59
def prefixEnd_6812282 : Nat := 4983230072969 + 3 ^ 40 * 6812282 * 2
def baseEnd_6812282 : Nat := 3497975019972021149045891

theorem tailTrace_6812282 : CollatzResearch.WordTrace tailWord_6812282 prefixEnd_6812282 3497975019972021149045891 := by
  unfold tailWord_6812282
  simp only [CollatzResearch.WordTrace]
  refine ⟨62116084176568308496027775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165642891137515489322740733 62116084176568308496027775)
  ·
    refine ⟨93174126264852462744041663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62116084176568308496027775 93174126264852462744041663)
    ·
      refine ⟨139761189397278694116062495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93174126264852462744041663 139761189397278694116062495)
      ·
        refine ⟨209641784095918041174093743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139761189397278694116062495 209641784095918041174093743)
        ·
          refine ⟨314462676143877061761140615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209641784095918041174093743 314462676143877061761140615)
          ·
            refine ⟨471694014215815592641710923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314462676143877061761140615 471694014215815592641710923)
            ·
              refine ⟨707541021323723388962566385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471694014215815592641710923 707541021323723388962566385)
              ·
                refine ⟨530655765992792541721924789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 707541021323723388962566385 530655765992792541721924789)
                ·
                  refine ⟨49748978061824300786430449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 530655765992792541721924789 49748978061824300786430449)
                  ·
                    refine ⟨37311733546368225589822837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49748978061824300786430449 37311733546368225589822837)
                    ·
                      refine ⟨3497975019972021149045891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37311733546368225589822837 3497975019972021149045891)
                      ·
                        rfl

theorem cell23_6812282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_6812282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812282 prefixEnd_6812282 := by exact prefixLift 6812282
  have htrace : WordTrace (prefixWord ++ tailWord_6812282) baseStart_6812282 baseEnd_6812282 := by
    simpa [prefixWord, tailWord_6812282, baseEnd_6812282] using wordTrace_append hprefix tailTrace_6812282
  have hstable : (prefixWord ++ tailWord_6812282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812282).length < 2 ^ (prefixWord ++ tailWord_6812282).sum := by decide
  have hdescent : baseEnd_6812282 < baseStart_6812282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812329 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_6812329 : Nat := 118140960795 + 6812329 * 2 ^ 59
def prefixEnd_6812329 : Nat := 4983230072969 + 3 ^ 40 * 6812329 * 2
def baseEnd_6812329 : Nat := 3497999153562782465158175

theorem tailTrace_6812329 : CollatzResearch.WordTrace tailWord_6812329 prefixEnd_6812329 3497999153562782465158175 := by
  unfold tailWord_6812329
  simp only [CollatzResearch.WordTrace]
  refine ⟨248466050937102961011072041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165644033958068640674048027 248466050937102961011072041)
  ·
    refine ⟨186349538202827220758304031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248466050937102961011072041 186349538202827220758304031)
    ·
      refine ⟨279524307304240831137456047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186349538202827220758304031 279524307304240831137456047)
      ·
        refine ⟨419286460956361246706184071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279524307304240831137456047 419286460956361246706184071)
        ·
          refine ⟨628929691434541870059276107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419286460956361246706184071 628929691434541870059276107)
          ·
            refine ⟨943394537151812805088914161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628929691434541870059276107 943394537151812805088914161)
            ·
              refine ⟨707545902863859603816685621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943394537151812805088914161 707545902863859603816685621)
              ·
                refine ⟨66332428393486837857814277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 707545902863859603816685621 66332428393486837857814277)
                ·
                  refine ⟨12437330323778782098340177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66332428393486837857814277 12437330323778782098340177)
                  ·
                    refine ⟨9327997742834086573755133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12437330323778782098340177 9327997742834086573755133)
                    ·
                      refine ⟨3497999153562782465158175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9327997742834086573755133 3497999153562782465158175)
                      ·
                        rfl

theorem cell23_6812329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_6812329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812329 prefixEnd_6812329 := by exact prefixLift 6812329
  have htrace : WordTrace (prefixWord ++ tailWord_6812329) baseStart_6812329 baseEnd_6812329 := by
    simpa [prefixWord, tailWord_6812329, baseEnd_6812329] using wordTrace_append hprefix tailTrace_6812329
  have hstable : (prefixWord ++ tailWord_6812329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812329).length < 2 ^ (prefixWord ++ tailWord_6812329).sum := by decide
  have hdescent : baseEnd_6812329 < baseStart_6812329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812387 : List Nat := [1, 1, 1, 7, 1, 3, 2, 2, 1, 4]
def baseStart_6812387 : Nat := 118140960795 + 6812387 * 2 ^ 59
def prefixEnd_6812387 : Nat := 4983230072969 + 3 ^ 40 * 6812387 * 2
def baseEnd_6812387 : Nat := 1166009645146914412744303

theorem tailTrace_6812387 : CollatzResearch.WordTrace tailWord_6812387 prefixEnd_6812387 1166009645146914412744303 := by
  unfold tailWord_6812387
  simp only [CollatzResearch.WordTrace]
  refine ⟨248468166370892836916683415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165645444247261891277788943 248468166370892836916683415)
  ·
    refine ⟨372702249556339255375025123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248468166370892836916683415 372702249556339255375025123)
    ·
      refine ⟨559053374334508883062537685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372702249556339255375025123 559053374334508883062537685)
      ·
        refine ⟨13102813460965051946778227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 559053374334508883062537685 13102813460965051946778227)
        ·
          refine ⟨19654220191447577920167341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13102813460965051946778227 19654220191447577920167341)
          ·
            refine ⟨7370332571792841720062753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19654220191447577920167341 7370332571792841720062753)
            ·
              refine ⟨5527749428844631290047065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7370332571792841720062753 5527749428844631290047065)
              ·
                refine ⟨4145812071633473467535299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5527749428844631290047065 4145812071633473467535299)
                ·
                  refine ⟨6218718107450210201302949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145812071633473467535299 6218718107450210201302949)
                  ·
                    refine ⟨1166009645146914412744303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218718107450210201302949 1166009645146914412744303)
                    ·
                      rfl

theorem cell23_6812387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 2, 2, 1, 4].length) (baseStart_6812387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812387 prefixEnd_6812387 := by exact prefixLift 6812387
  have htrace : WordTrace (prefixWord ++ tailWord_6812387) baseStart_6812387 baseEnd_6812387 := by
    simpa [prefixWord, tailWord_6812387, baseEnd_6812387] using wordTrace_append hprefix tailTrace_6812387
  have hstable : (prefixWord ++ tailWord_6812387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812387).length < 2 ^ (prefixWord ++ tailWord_6812387).sum := by decide
  have hdescent : baseEnd_6812387 < baseStart_6812387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812426 : List Nat := [3, 1, 2, 2, 1, 2, 2, 2, 4, 4]
def baseStart_6812426 : Nat := 118140960795 + 6812426 * 2 ^ 59
def prefixEnd_6812426 : Nat := 4983230072969 + 3 ^ 40 * 6812426 * 2
def baseEnd_6812426 : Nat := 1166016320395422861881743

theorem tailTrace_6812426 : CollatzResearch.WordTrace tailWord_6812426 prefixEnd_6812426 1166016320395422861881743 := by
  unfold tailWord_6812426
  simp only [CollatzResearch.WordTrace]
  refine ⟨62117397204437886644338283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165646392545167697718235421 62117397204437886644338283)
  ·
    refine ⟨93176095806656829966507425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62117397204437886644338283 93176095806656829966507425)
    ·
      refine ⟨69882071854992622474880569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93176095806656829966507425 69882071854992622474880569)
      ·
        refine ⟨52411553891244466856160427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69882071854992622474880569 52411553891244466856160427)
        ·
          refine ⟨78617330836866700284240641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52411553891244466856160427 78617330836866700284240641)
          ·
            refine ⟨58962998127650025213180481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78617330836866700284240641 58962998127650025213180481)
            ·
              refine ⟨44222248595737518909885361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58962998127650025213180481 44222248595737518909885361)
              ·
                refine ⟨33166686446803139182414021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44222248595737518909885361 33166686446803139182414021)
                ·
                  refine ⟨6218753708775588596702629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33166686446803139182414021 6218753708775588596702629)
                  ·
                    refine ⟨1166016320395422861881743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218753708775588596702629 1166016320395422861881743)
                    ·
                      rfl

theorem cell23_6812426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_6812426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812426 prefixEnd_6812426 := by exact prefixLift 6812426
  have htrace : WordTrace (prefixWord ++ tailWord_6812426) baseStart_6812426 baseEnd_6812426 := by
    simpa [prefixWord, tailWord_6812426, baseEnd_6812426] using wordTrace_append hprefix tailTrace_6812426
  have hstable : (prefixWord ++ tailWord_6812426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812426).length < 2 ^ (prefixWord ++ tailWord_6812426).sum := by decide
  have hdescent : baseEnd_6812426 < baseStart_6812426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812433 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 1, 1, 4]
def baseStart_6812433 : Nat := 118140960795 + 6812433 * 2 ^ 59
def prefixEnd_6812433 : Nat := 4983230072969 + 3 ^ 40 * 6812433 * 2
def baseEnd_6812433 : Nat := 3498052555550850058257697

theorem tailTrace_6812433 : CollatzResearch.WordTrace tailWord_6812433 prefixEnd_6812433 3498052555550850058257697 := by
  unfold tailWord_6812433
  simp only [CollatzResearch.WordTrace]
  refine ⟨248469844128726186772857953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165646562752484124515238635 248469844128726186772857953)
  ·
    refine ⟨186352383096544640079643465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248469844128726186772857953 186352383096544640079643465)
    ·
      refine ⟨139764287322408480059732599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186352383096544640079643465 139764287322408480059732599)
      ·
        refine ⟨209646430983612720089598899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139764287322408480059732599 209646430983612720089598899)
        ·
          refine ⟨314469646475419080134398349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209646430983612720089598899 314469646475419080134398349)
          ·
            refine ⟨117926117428282155050399381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314469646475419080134398349 117926117428282155050399381)
            ·
              refine ⟨5527786754450726017987471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117926117428282155050399381 5527786754450726017987471)
              ·
                refine ⟨8291680131676089026981207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527786754450726017987471 8291680131676089026981207)
                ·
                  refine ⟨12437520197514133540471811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8291680131676089026981207 12437520197514133540471811)
                  ·
                    refine ⟨18656280296271200310707717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12437520197514133540471811 18656280296271200310707717)
                    ·
                      refine ⟨3498052555550850058257697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18656280296271200310707717 3498052555550850058257697)
                      ·
                        rfl

theorem cell23_6812433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_6812433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812433 prefixEnd_6812433 := by exact prefixLift 6812433
  have htrace : WordTrace (prefixWord ++ tailWord_6812433) baseStart_6812433 baseEnd_6812433 := by
    simpa [prefixWord, tailWord_6812433, baseEnd_6812433] using wordTrace_append hprefix tailTrace_6812433
  have hstable : (prefixWord ++ tailWord_6812433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812433).length < 2 ^ (prefixWord ++ tailWord_6812433).sum := by decide
  have hdescent : baseEnd_6812433 < baseStart_6812433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812450 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_6812450 : Nat := 118140960795 + 6812450 * 2 ^ 59
def prefixEnd_6812450 : Nat := 4983230072969 + 3 ^ 40 * 6812450 * 2
def baseEnd_6812450 : Nat := 3498061284721976491745119

theorem tailTrace_6812450 : CollatzResearch.WordTrace tailWord_6812450 prefixEnd_6812450 3498061284721976491745119 := by
  unfold tailWord_6812450
  simp only [CollatzResearch.WordTrace]
  refine ⟨62117616042416149669056701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165646976113109732450817869 62117616042416149669056701)
  ·
    refine ⟨23294106015906056125896263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62117616042416149669056701 23294106015906056125896263)
    ·
      refine ⟨34941159023859084188844395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23294106015906056125896263 34941159023859084188844395)
      ·
        refine ⟨52411738535788626283266593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34941159023859084188844395 52411738535788626283266593)
        ·
          refine ⟨39308803901841469712449945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52411738535788626283266593 39308803901841469712449945)
          ·
            refine ⟨29481602926381102284337459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39308803901841469712449945 29481602926381102284337459)
            ·
              refine ⟨44222404389571653426506189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29481602926381102284337459 44222404389571653426506189)
              ·
                refine ⟨16583401646089370034939821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44222404389571653426506189 16583401646089370034939821)
                ·
                  refine ⟨6218775617283513763102433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16583401646089370034939821 6218775617283513763102433)
                  ·
                    refine ⟨4664081712962635322326825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6218775617283513763102433 4664081712962635322326825)
                    ·
                      refine ⟨3498061284721976491745119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664081712962635322326825 3498061284721976491745119)
                      ·
                        rfl

theorem cell23_6812450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_6812450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812450 prefixEnd_6812450 := by exact prefixLift 6812450
  have htrace : WordTrace (prefixWord ++ tailWord_6812450) baseStart_6812450 baseEnd_6812450 := by
    simpa [prefixWord, tailWord_6812450, baseEnd_6812450] using wordTrace_append hprefix tailTrace_6812450
  have hstable : (prefixWord ++ tailWord_6812450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812450).length < 2 ^ (prefixWord ++ tailWord_6812450).sum := by decide
  have hdescent : baseEnd_6812450 < baseStart_6812450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812499 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 4, 6]
def baseStart_6812499 : Nat := 118140960795 + 6812499 * 2 ^ 59
def prefixEnd_6812499 : Nat := 4983230072969 + 3 ^ 40 * 6812499 * 2
def baseEnd_6812499 : Nat := 1166028815091348933344131

theorem tailTrace_6812499 : CollatzResearch.WordTrace tailWord_6812499 prefixEnd_6812499 1166028815091348933344131 := by
  unfold tailWord_6812499
  simp only [CollatzResearch.WordTrace]
  refine ⟨248472251346487080044760551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165648167564324720029840367 248472251346487080044760551)
  ·
    refine ⟨372708377019730620067140827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248472251346487080044760551 372708377019730620067140827)
    ·
      refine ⟨559062565529595930100711241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372708377019730620067140827 559062565529595930100711241)
      ·
        refine ⟨419296924147196947575533431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559062565529595930100711241 419296924147196947575533431)
        ·
          refine ⟨628945386220795421363300147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419296924147196947575533431 628945386220795421363300147)
          ·
            refine ⟨943418079331193132044950221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628945386220795421363300147 943418079331193132044950221)
            ·
              refine ⟨353781779749197424516856333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943418079331193132044950221 353781779749197424516856333)
              ·
                refine ⟨132668167405949034193821125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353781779749197424516856333 132668167405949034193821125)
                ·
                  refine ⟨24875281388615443911341461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132668167405949034193821125 24875281388615443911341461)
                  ·
                    refine ⟨1166028815091348933344131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24875281388615443911341461 1166028815091348933344131)
                    ·
                      rfl

theorem cell23_6812499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 6].length) (baseStart_6812499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812499 prefixEnd_6812499 := by exact prefixLift 6812499
  have htrace : WordTrace (prefixWord ++ tailWord_6812499) baseStart_6812499 baseEnd_6812499 := by
    simpa [prefixWord, tailWord_6812499, baseEnd_6812499] using wordTrace_append hprefix tailTrace_6812499
  have hstable : (prefixWord ++ tailWord_6812499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812499).length < 2 ^ (prefixWord ++ tailWord_6812499).sum := by decide
  have hdescent : baseEnd_6812499 < baseStart_6812499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812573 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 3]
def baseStart_6812573 : Nat := 118140960795 + 6812573 * 2 ^ 59
def prefixEnd_6812573 : Nat := 4983230072969 + 3 ^ 40 * 6812573 * 2
def baseEnd_6812573 : Nat := 3498124442842479510507053

theorem tailTrace_6812573 : CollatzResearch.WordTrace tailWord_6812573 prefixEnd_6812573 3498124442842479510507053 := by
  unfold tailWord_6812573
  simp only [CollatzResearch.WordTrace]
  refine ⟨248474950348218990682954373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165649966898812660455302915 248474950348218990682954373)
  ·
    refine ⟨46589053190291060753053945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248474950348218990682954373 46589053190291060753053945)
    ·
      refine ⟨34941789892718295564790459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46589053190291060753053945 34941789892718295564790459)
      ·
        refine ⟨52412684839077443347185689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34941789892718295564790459 52412684839077443347185689)
        ·
          refine ⟨39309513629308082510389267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52412684839077443347185689 39309513629308082510389267)
          ·
            refine ⟨58964270443962123765583901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39309513629308082510389267 58964270443962123765583901)
            ·
              refine ⟨22111601416485796412093963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58964270443962123765583901 22111601416485796412093963)
              ·
                refine ⟨33167402124728694618140945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22111601416485796412093963 33167402124728694618140945)
                ·
                  refine ⟨24875551593546520963605709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33167402124728694618140945 24875551593546520963605709)
                  ·
                    refine ⟨9328331847579945361352141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24875551593546520963605709 9328331847579945361352141)
                    ·
                      refine ⟨3498124442842479510507053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9328331847579945361352141 3498124442842479510507053)
                      ·
                        rfl

theorem cell23_6812573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_6812573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812573 prefixEnd_6812573 := by exact prefixLift 6812573
  have htrace : WordTrace (prefixWord ++ tailWord_6812573) baseStart_6812573 baseEnd_6812573 := by
    simpa [prefixWord, tailWord_6812573, baseEnd_6812573] using wordTrace_append hprefix tailTrace_6812573
  have hstable : (prefixWord ++ tailWord_6812573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812573).length < 2 ^ (prefixWord ++ tailWord_6812573).sum := by decide
  have hdescent : baseEnd_6812573 < baseStart_6812573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812576 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 4, 5]
def baseStart_6812576 : Nat := 118140960795 + 6812576 * 2 ^ 59
def prefixEnd_6812576 : Nat := 4983230072969 + 3 ^ 40 * 6812576 * 2
def baseEnd_6812576 : Nat := 1166041994428147666256513

theorem tailTrace_6812576 : CollatzResearch.WordTrace tailWord_6812576 prefixEnd_6812576 1166041994428147666256513 := by
  unfold tailWord_6812576
  simp only [CollatzResearch.WordTrace]
  refine ⟨124237529883604061097656791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165650039844805414796875721 124237529883604061097656791)
  ·
    refine ⟨186356294825406091646485187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124237529883604061097656791 186356294825406091646485187)
    ·
      refine ⟨279534442238109137469727781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186356294825406091646485187 279534442238109137469727781)
      ·
        refine ⟨52412707919645463275573959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279534442238109137469727781 52412707919645463275573959)
        ·
          refine ⟨78619061879468194913360939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52412707919645463275573959 78619061879468194913360939)
          ·
            refine ⟨117928592819202292370041409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78619061879468194913360939 117928592819202292370041409)
            ·
              refine ⟨88446444614401719277531057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117928592819202292370041409 88446444614401719277531057)
              ·
                refine ⟨66334833460801289458148293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88446444614401719277531057 66334833460801289458148293)
                ·
                  refine ⟨12437781273900241773402805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66334833460801289458148293 12437781273900241773402805)
                  ·
                    refine ⟨1166041994428147666256513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12437781273900241773402805 1166041994428147666256513)
                    ·
                      rfl

theorem cell23_6812576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 4, 5].length) (baseStart_6812576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812576 prefixEnd_6812576 := by exact prefixLift 6812576
  have htrace : WordTrace (prefixWord ++ tailWord_6812576) baseStart_6812576 baseEnd_6812576 := by
    simpa [prefixWord, tailWord_6812576, baseEnd_6812576] using wordTrace_append hprefix tailTrace_6812576
  have hstable : (prefixWord ++ tailWord_6812576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812576).length < 2 ^ (prefixWord ++ tailWord_6812576).sum := by decide
  have hdescent : baseEnd_6812576 < baseStart_6812576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812593 : List Nat := [1, 2, 2, 4, 3, 1, 1, 1, 1, 7]
def baseStart_6812593 : Nat := 118140960795 + 6812593 * 2 ^ 59
def prefixEnd_6812593 : Nat := 4983230072969 + 3 ^ 40 * 6812593 * 2
def baseEnd_6812593 : Nat := 1166044904151856477418987

theorem tailTrace_6812593 : CollatzResearch.WordTrace tailWord_6812593 prefixEnd_6812593 1166044904151856477418987 := by
  unfold tailWord_6812593
  simp only [CollatzResearch.WordTrace]
  refine ⟨248475679808146534098682433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165650453205431022732454955 248475679808146534098682433)
  ·
    refine ⟨186356759856109900574011825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248475679808146534098682433 186356759856109900574011825)
    ·
      refine ⟨139767569892082425430508869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186356759856109900574011825 139767569892082425430508869)
      ·
        refine ⟨26206419354765454768220413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139767569892082425430508869 26206419354765454768220413)
        ·
          refine ⟨9827407258037045538082655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26206419354765454768220413 9827407258037045538082655)
          ·
            refine ⟨14741110887055568307123983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9827407258037045538082655 14741110887055568307123983)
            ·
              refine ⟨22111666330583352460685975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14741110887055568307123983 22111666330583352460685975)
              ·
                refine ⟨33167499495875028691028963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22111666330583352460685975 33167499495875028691028963)
                ·
                  refine ⟨49751249243812543036543445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33167499495875028691028963 49751249243812543036543445)
                  ·
                    refine ⟨1166044904151856477418987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49751249243812543036543445 1166044904151856477418987)
                    ·
                      rfl

theorem cell23_6812593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_6812593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812593 prefixEnd_6812593 := by exact prefixLift 6812593
  have htrace : WordTrace (prefixWord ++ tailWord_6812593) baseStart_6812593 baseEnd_6812593 := by
    simpa [prefixWord, tailWord_6812593, baseEnd_6812593] using wordTrace_append hprefix tailTrace_6812593
  have hstable : (prefixWord ++ tailWord_6812593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812593).length < 2 ^ (prefixWord ++ tailWord_6812593).sum := by decide
  have hdescent : baseEnd_6812593 < baseStart_6812593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812623 : List Nat := [1, 1, 2, 1, 1, 6, 1, 3, 3, 4]
def baseStart_6812623 : Nat := 118140960795 + 6812623 * 2 ^ 59
def prefixEnd_6812623 : Nat := 4983230072969 + 3 ^ 40 * 6812623 * 2
def baseEnd_6812623 : Nat := 1166050038958401438293941

theorem tailTrace_6812623 : CollatzResearch.WordTrace tailWord_6812623 prefixEnd_6812623 1166050038958401438293941 := by
  unfold tailWord_6812623
  simp only [CollatzResearch.WordTrace]
  refine ⟨248476773998037849222274523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165651182665358566148183015 248476773998037849222274523)
  ·
    refine ⟨372715160997056773833411785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248476773998037849222274523 372715160997056773833411785)
    ·
      refine ⟨279536370747792580375058839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372715160997056773833411785 279536370747792580375058839)
      ·
        refine ⟨419304556121688870562588259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279536370747792580375058839 419304556121688870562588259)
        ·
          refine ⟨628956834182533305843882389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419304556121688870562588259 628956834182533305843882389)
          ·
            refine ⟨29482351602306248711431987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 628956834182533305843882389 29482351602306248711431987)
            ·
              refine ⟨44223527403459373067147981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29482351602306248711431987 44223527403459373067147981)
              ·
                refine ⟨16583822776297264900180493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44223527403459373067147981 16583822776297264900180493)
                ·
                  refine ⟨6218933541111474337567685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16583822776297264900180493 6218933541111474337567685)
                  ·
                    refine ⟨1166050038958401438293941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218933541111474337567685 1166050038958401438293941)
                    ·
                      rfl

theorem cell23_6812623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 4].length) (baseStart_6812623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812623 prefixEnd_6812623 := by exact prefixLift 6812623
  have htrace : WordTrace (prefixWord ++ tailWord_6812623) baseStart_6812623 baseEnd_6812623 := by
    simpa [prefixWord, tailWord_6812623, baseEnd_6812623] using wordTrace_append hprefix tailTrace_6812623
  have hstable : (prefixWord ++ tailWord_6812623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812623).length < 2 ^ (prefixWord ++ tailWord_6812623).sum := by decide
  have hdescent : baseEnd_6812623 < baseStart_6812623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812630 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4]
def baseStart_6812630 : Nat := 118140960795 + 6812630 * 2 ^ 59
def prefixEnd_6812630 : Nat := 4983230072969 + 3 ^ 40 * 6812630 * 2
def baseEnd_6812630 : Nat := 3498153711239785787494291

theorem tailTrace_6812630 : CollatzResearch.WordTrace tailWord_6812630 prefixEnd_6812630 3498153711239785787494291 := by
  unfold tailWord_6812630
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529814331813280588611209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165651352872674992945186229 15529814331813280588611209)
  ·
    refine ⟨11647360748859960441458407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15529814331813280588611209 11647360748859960441458407)
    ·
      refine ⟨17471041123289940662187611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11647360748859960441458407 17471041123289940662187611)
      ·
        refine ⟨26206561684934910993281417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17471041123289940662187611 26206561684934910993281417)
        ·
          refine ⟨19654921263701183244961063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26206561684934910993281417 19654921263701183244961063)
          ·
            refine ⟨29482381895551774867441595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19654921263701183244961063 29482381895551774867441595)
            ·
              refine ⟨44223572843327662301162393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29482381895551774867441595 44223572843327662301162393)
              ·
                refine ⟨33167679632495746725871795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44223572843327662301162393 33167679632495746725871795)
                ·
                  refine ⟨49751519448743620088807693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33167679632495746725871795 49751519448743620088807693)
                  ·
                    refine ⟨18656819793278857533302885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49751519448743620088807693 18656819793278857533302885)
                    ·
                      refine ⟨3498153711239785787494291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18656819793278857533302885 3498153711239785787494291)
                      ·
                        rfl

theorem cell23_6812630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_6812630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812630 prefixEnd_6812630 := by exact prefixLift 6812630
  have htrace : WordTrace (prefixWord ++ tailWord_6812630) baseStart_6812630 baseEnd_6812630 := by
    simpa [prefixWord, tailWord_6812630, baseEnd_6812630] using wordTrace_append hprefix tailTrace_6812630
  have hstable : (prefixWord ++ tailWord_6812630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812630).length < 2 ^ (prefixWord ++ tailWord_6812630).sum := by decide
  have hdescent : baseEnd_6812630 < baseStart_6812630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812633 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_6812633 : Nat := 118140960795 + 6812633 * 2 ^ 59
def prefixEnd_6812633 : Nat := 4983230072969 + 3 ^ 40 * 6812633 * 2
def baseEnd_6812633 : Nat := 3498155251681749275756777

theorem tailTrace_6812633 : CollatzResearch.WordTrace tailWord_6812633 prefixEnd_6812633 3498155251681749275756777 := by
  unfold tailWord_6812633
  simp only [CollatzResearch.WordTrace]
  refine ⟨248477138728001620930138553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165651425818667747286759035 248477138728001620930138553)
  ·
    refine ⟨186357854046001215697603915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248477138728001620930138553 186357854046001215697603915)
    ·
      refine ⟨279536781069001823546405873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186357854046001215697603915 279536781069001823546405873)
      ·
        refine ⟨209652585801751367659804405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279536781069001823546405873 209652585801751367659804405)
        ·
          refine ⟨19654929918914190718106663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209652585801751367659804405 19654929918914190718106663)
          ·
            refine ⟨29482394878371286077159995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19654929918914190718106663 29482394878371286077159995)
            ·
              refine ⟨44223592317556929115739993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29482394878371286077159995 44223592317556929115739993)
              ·
                refine ⟨33167694238167696836804995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44223592317556929115739993 33167694238167696836804995)
                ·
                  refine ⟨49751541357251545255207493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33167694238167696836804995 49751541357251545255207493)
                  ·
                    refine ⟨9328414004484664735351405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49751541357251545255207493 9328414004484664735351405)
                    ·
                      refine ⟨3498155251681749275756777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9328414004484664735351405 3498155251681749275756777)
                      ·
                        rfl

theorem cell23_6812633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_6812633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812633 prefixEnd_6812633 := by exact prefixLift 6812633
  have htrace : WordTrace (prefixWord ++ tailWord_6812633) baseStart_6812633 baseEnd_6812633 := by
    simpa [prefixWord, tailWord_6812633, baseEnd_6812633] using wordTrace_append hprefix tailTrace_6812633
  have hstable : (prefixWord ++ tailWord_6812633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812633).length < 2 ^ (prefixWord ++ tailWord_6812633).sum := by decide
  have hdescent : baseEnd_6812633 < baseStart_6812633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812657 : List Nat := [1, 2, 2, 2, 4, 1, 3, 3, 1, 4]
def baseStart_6812657 : Nat := 118140960795 + 6812657 * 2 ^ 59
def prefixEnd_6812657 : Nat := 4983230072969 + 3 ^ 40 * 6812657 * 2
def baseEnd_6812657 : Nat := 1166055858405819060618889

theorem tailTrace_6812657 : CollatzResearch.WordTrace tailWord_6812657 prefixEnd_6812657 1166055858405819060618889 := by
  unfold tailWord_6812657
  simp only [CollatzResearch.WordTrace]
  refine ⟨248478014079914673029012225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165652009386609782019341483 248478014079914673029012225)
  ·
    refine ⟨186358510559936004771759169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248478014079914673029012225 186358510559936004771759169)
    ·
      refine ⟨139768882919952003578819377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186358510559936004771759169 139768882919952003578819377)
      ·
        refine ⟨104826662189964002684114533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139768882919952003578819377 104826662189964002684114533)
        ·
          refine ⟨19654999160618250503271475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104826662189964002684114533 19654999160618250503271475)
          ·
            refine ⟨29482498740927375754907213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19654999160618250503271475 29482498740927375754907213)
            ·
              refine ⟨11055937027847765908090205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29482498740927375754907213 11055937027847765908090205)
              ·
                refine ⟨4145976385442912215533827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11055937027847765908090205 4145976385442912215533827)
                ·
                  refine ⟨6218964578164368323300741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4145976385442912215533827 6218964578164368323300741)
                  ·
                    refine ⟨1166055858405819060618889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6218964578164368323300741 1166055858405819060618889)
                    ·
                      rfl

theorem cell23_6812657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_6812657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812657 prefixEnd_6812657 := by exact prefixLift 6812657
  have htrace : WordTrace (prefixWord ++ tailWord_6812657) baseStart_6812657 baseEnd_6812657 := by
    simpa [prefixWord, tailWord_6812657, baseEnd_6812657] using wordTrace_append hprefix tailTrace_6812657
  have hstable : (prefixWord ++ tailWord_6812657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812657).length < 2 ^ (prefixWord ++ tailWord_6812657).sum := by decide
  have hdescent : baseEnd_6812657 < baseStart_6812657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812700 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6812700 : Nat := 118140960795 + 6812700 * 2 ^ 59
def prefixEnd_6812700 : Nat := 4983230072969 + 3 ^ 40 * 6812700 * 2
def baseEnd_6812700 : Nat := 1166063218295200171206323

theorem tailTrace_6812700 : CollatzResearch.WordTrace tailWord_6812700 prefixEnd_6812700 1166063218295200171206323 := by
  unfold tailWord_6812700
  simp only [CollatzResearch.WordTrace]
  refine ⟨124239791209379445686413777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165653054945839260915218369 124239791209379445686413777)
  ·
    refine ⟨93179843407034584264810333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124239791209379445686413777 93179843407034584264810333)
    ·
      refine ⟨34942441277637969099303875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93179843407034584264810333 34942441277637969099303875)
      ·
        refine ⟨52413661916456953648955813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34942441277637969099303875 52413661916456953648955813)
        ·
          refine ⟨9827561609335678809179215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52413661916456953648955813 9827561609335678809179215)
          ·
            refine ⟨14741342414003518213768823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9827561609335678809179215 14741342414003518213768823)
            ·
              refine ⟨22112013621005277320653235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14741342414003518213768823 22112013621005277320653235)
              ·
                refine ⟨33168020431507915980979853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22112013621005277320653235 33168020431507915980979853)
                ·
                  refine ⟨12438007661815468492867445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33168020431507915980979853 12438007661815468492867445)
                  ·
                    refine ⟨1166063218295200171206323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12438007661815468492867445 1166063218295200171206323)
                    ·
                      rfl

theorem cell23_6812700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6812700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812700 prefixEnd_6812700 := by exact prefixLift 6812700
  have htrace : WordTrace (prefixWord ++ tailWord_6812700) baseStart_6812700 baseEnd_6812700 := by
    simpa [prefixWord, tailWord_6812700, baseEnd_6812700] using wordTrace_append hprefix tailTrace_6812700
  have hstable : (prefixWord ++ tailWord_6812700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812700).length < 2 ^ (prefixWord ++ tailWord_6812700).sum := by decide
  have hdescent : baseEnd_6812700 < baseStart_6812700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812707 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 2, 3, 2]
def baseStart_6812707 : Nat := 118140960795 + 6812707 * 2 ^ 59
def prefixEnd_6812707 : Nat := 4983230072969 + 3 ^ 40 * 6812707 * 2
def baseEnd_6812707 : Nat := 3498193249250181986231437

theorem tailTrace_6812707 : CollatzResearch.WordTrace tailWord_6812707 prefixEnd_6812707 3498193249250181986231437 := by
  unfold tailWord_6812707
  simp only [CollatzResearch.WordTrace]
  refine ⟨248479837729733531568332375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165653225153155687712221583 248479837729733531568332375)
  ·
    refine ⟨372719756594600297352498563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248479837729733531568332375 372719756594600297352498563)
    ·
      refine ⟨559079634891900446028747845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372719756594600297352498563 559079634891900446028747845)
      ·
        refine ⟨104827431542231333630390221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 559079634891900446028747845 104827431542231333630390221)
        ·
          refine ⟨39310286828336750111396333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104827431542231333630390221 39310286828336750111396333)
          ·
            refine ⟨14741357560626281291773625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39310286828336750111396333 14741357560626281291773625)
            ·
              refine ⟨11056018170469710968830219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14741357560626281291773625 11056018170469710968830219)
              ·
                refine ⟨16584027255704566453245329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056018170469710968830219 16584027255704566453245329)
                ·
                  refine ⟨12438020441778424839933997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16584027255704566453245329 12438020441778424839933997)
                  ·
                    refine ⟨4664257665666909314975249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12438020441778424839933997 4664257665666909314975249)
                    ·
                      refine ⟨3498193249250181986231437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664257665666909314975249 3498193249250181986231437)
                      ·
                        rfl

theorem cell23_6812707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_6812707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812707 prefixEnd_6812707 := by exact prefixLift 6812707
  have htrace : WordTrace (prefixWord ++ tailWord_6812707) baseStart_6812707 baseEnd_6812707 := by
    simpa [prefixWord, tailWord_6812707, baseEnd_6812707] using wordTrace_append hprefix tailTrace_6812707
  have hstable : (prefixWord ++ tailWord_6812707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812707).length < 2 ^ (prefixWord ++ tailWord_6812707).sum := by decide
  have hdescent : baseEnd_6812707 < baseStart_6812707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812724 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_6812724 : Nat := 118140960795 + 6812724 * 2 ^ 59
def prefixEnd_6812724 : Nat := 4983230072969 + 3 ^ 40 * 6812724 * 2
def baseEnd_6812724 : Nat := 3498201978421308419718859

theorem tailTrace_6812724 : CollatzResearch.WordTrace tailWord_6812724 prefixEnd_6812724 3498201978421308419718859 := by
  unfold tailWord_6812724
  simp only [CollatzResearch.WordTrace]
  refine ⟨124240228885335971735850613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165653638513781295647800817 124240228885335971735850613)
  ·
    refine ⟨11647521458000247350235995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124240228885335971735850613 11647521458000247350235995)
    ·
      refine ⟨17471282187000371025353993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11647521458000247350235995 17471282187000371025353993)
      ·
        refine ⟨13103461640250278269015495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17471282187000371025353993 13103461640250278269015495)
        ·
          refine ⟨19655192460375417403523243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13103461640250278269015495 19655192460375417403523243)
          ·
            refine ⟨29482788690563126105284865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19655192460375417403523243 29482788690563126105284865)
            ·
              refine ⟨22112091517922344578963649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29482788690563126105284865 22112091517922344578963649)
              ·
                refine ⟨16584068638441758434222737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22112091517922344578963649 16584068638441758434222737)
                ·
                  refine ⟨12438051478831318825667053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16584068638441758434222737 12438051478831318825667053)
                  ·
                    refine ⟨4664269304561744559625145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12438051478831318825667053 4664269304561744559625145)
                    ·
                      refine ⟨3498201978421308419718859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664269304561744559625145 3498201978421308419718859)
                      ·
                        rfl

theorem cell23_6812724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_6812724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812724 prefixEnd_6812724 := by exact prefixLift 6812724
  have htrace : WordTrace (prefixWord ++ tailWord_6812724) baseStart_6812724 baseEnd_6812724 := by
    simpa [prefixWord, tailWord_6812724, baseEnd_6812724] using wordTrace_append hprefix tailTrace_6812724
  have hstable : (prefixWord ++ tailWord_6812724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812724).length < 2 ^ (prefixWord ++ tailWord_6812724).sum := by decide
  have hdescent : baseEnd_6812724 < baseStart_6812724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812730 : List Nat := [3, 1, 1, 1, 3, 1, 3, 4, 2, 4]
def baseStart_6812730 : Nat := 118140960795 + 6812730 * 2 ^ 59
def prefixEnd_6812730 : Nat := 4983230072969 + 3 ^ 40 * 6812730 * 2
def baseEnd_6812730 : Nat := 1166068353101745132081277

theorem tailTrace_6812730 : CollatzResearch.WordTrace tailWord_6812730 prefixEnd_6812730 1166068353101745132081277 := by
  unfold tailWord_6812730
  simp only [CollatzResearch.WordTrace]
  refine ⟨62120169152162551624104911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165653784405766804330946429 62120169152162551624104911)
  ·
    refine ⟨93180253728243827436157367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62120169152162551624104911 93180253728243827436157367)
    ·
      refine ⟨139770380592365741154236051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93180253728243827436157367 139770380592365741154236051)
      ·
        refine ⟨209655570888548611731354077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139770380592365741154236051 209655570888548611731354077)
        ·
          refine ⟨78620839083205729399257779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209655570888548611731354077 78620839083205729399257779)
          ·
            refine ⟨117931258624808594098886669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78620839083205729399257779 117931258624808594098886669)
            ·
              refine ⟨44224221984303222787082501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117931258624808594098886669 44224221984303222787082501)
              ·
                refine ⟨8292041622056854272577969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44224221984303222787082501 8292041622056854272577969)
                ·
                  refine ⟨6219031216542640704433477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8292041622056854272577969 6219031216542640704433477)
                  ·
                    refine ⟨1166068353101745132081277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219031216542640704433477 1166068353101745132081277)
                    ·
                      rfl

theorem cell23_6812730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 4, 2, 4].length) (baseStart_6812730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812730 prefixEnd_6812730 := by exact prefixLift 6812730
  have htrace : WordTrace (prefixWord ++ tailWord_6812730) baseStart_6812730 baseEnd_6812730 := by
    simpa [prefixWord, tailWord_6812730, baseEnd_6812730] using wordTrace_append hprefix tailTrace_6812730
  have hstable : (prefixWord ++ tailWord_6812730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812730).length < 2 ^ (prefixWord ++ tailWord_6812730).sum := by decide
  have hdescent : baseEnd_6812730 < baseStart_6812730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812743 : List Nat := [1, 1, 4, 1, 3, 2, 3, 8]
def baseStart_6812743 : Nat := 118140960795 + 6812743 * 2 ^ 59
def prefixEnd_6812743 : Nat := 4983230072969 + 3 ^ 40 * 6812743 * 2
def baseEnd_6812743 : Nat := 129563397576064586865973

theorem tailTrace_6812743 : CollatzResearch.WordTrace tailWord_6812743 prefixEnd_6812743 129563397576064586865973 := by
  unfold tailWord_6812743
  simp only [CollatzResearch.WordTrace]
  refine ⟨248481150757603109716642883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165654100505068739811095255 248481150757603109716642883)
  ·
    refine ⟨372721726136404664574964325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248481150757603109716642883 372721726136404664574964325)
    ·
      refine ⟨69885323650575874607805811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372721726136404664574964325 69885323650575874607805811)
      ·
        refine ⟨104827985475863811911708717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69885323650575874607805811 104827985475863811911708717)
        ·
          refine ⟨39310494553448929466890769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104827985475863811911708717 39310494553448929466890769)
          ·
            refine ⟨29482870915086697100168077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39310494553448929466890769 29482870915086697100168077)
            ·
              refine ⟨11056076593157511412563029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29482870915086697100168077 11056076593157511412563029)
              ·
                refine ⟨129563397576064586865973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11056076593157511412563029 129563397576064586865973)
                ·
                  rfl

theorem cell23_6812743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 8].length) (baseStart_6812743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812743 prefixEnd_6812743 := by exact prefixLift 6812743
  have htrace : WordTrace (prefixWord ++ tailWord_6812743) baseStart_6812743 baseEnd_6812743 := by
    simpa [prefixWord, tailWord_6812743, baseEnd_6812743] using wordTrace_append hprefix tailTrace_6812743
  have hstable : (prefixWord ++ tailWord_6812743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812743).length < 2 ^ (prefixWord ++ tailWord_6812743).sum := by decide
  have hdescent : baseEnd_6812743 < baseStart_6812743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812750 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_6812750 : Nat := 118140960795 + 6812750 * 2 ^ 59
def prefixEnd_6812750 : Nat := 4983230072969 + 3 ^ 40 * 6812750 * 2
def baseEnd_6812750 : Nat := 3498215328918325317993739

theorem tailTrace_6812750 : CollatzResearch.WordTrace tailWord_6812750 prefixEnd_6812750 3498215328918325317993739 := by
  unfold tailWord_6812750
  simp only [CollatzResearch.WordTrace]
  refine ⟨31060175758572218739018463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165654270712385166608098469 31060175758572218739018463)
  ·
    refine ⟨46590263637858328108527695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31060175758572218739018463 46590263637858328108527695)
    ·
      refine ⟨69885395456787492162791543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46590263637858328108527695 69885395456787492162791543)
      ·
        refine ⟨104828093185181238244187315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69885395456787492162791543 104828093185181238244187315)
        ·
          refine ⟨157242139777771857366280973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104828093185181238244187315 157242139777771857366280973)
          ·
            refine ⟨58965802416664446512355365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157242139777771857366280973 58965802416664446512355365)
            ·
              refine ⟨11056087953124583721066631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58965802416664446512355365 11056087953124583721066631)
              ·
                refine ⟨16584131929686875581599947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056087953124583721066631 16584131929686875581599947)
                ·
                  refine ⟨24876197894530313372399921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16584131929686875581599947 24876197894530313372399921)
                  ·
                    refine ⟨18657148420897735029299941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24876197894530313372399921 18657148420897735029299941)
                    ·
                      refine ⟨3498215328918325317993739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18657148420897735029299941 3498215328918325317993739)
                      ·
                        rfl

theorem cell23_6812750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_6812750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812750 prefixEnd_6812750 := by exact prefixLift 6812750
  have htrace : WordTrace (prefixWord ++ tailWord_6812750) baseStart_6812750 baseEnd_6812750 := by
    simpa [prefixWord, tailWord_6812750, baseEnd_6812750] using wordTrace_append hprefix tailTrace_6812750
  have hstable : (prefixWord ++ tailWord_6812750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812750).length < 2 ^ (prefixWord ++ tailWord_6812750).sum := by decide
  have hdescent : baseEnd_6812750 < baseStart_6812750 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812754 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_6812754 : Nat := 118140960795 + 6812754 * 2 ^ 59
def prefixEnd_6812754 : Nat := 4983230072969 + 3 ^ 40 * 6812754 * 2
def baseEnd_6812754 : Nat := 3498217382840943302343721

theorem tailTrace_6812754 : CollatzResearch.WordTrace tailWord_6812754 prefixEnd_6812754 3498217382840943302343721 := by
  unfold tailWord_6812754
  simp only [CollatzResearch.WordTrace]
  refine ⟨62120387990140814648823329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165654367973708839063528877 62120387990140814648823329)
  ·
    refine ⟨46590290992605610986617497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62120387990140814648823329 46590290992605610986617497)
    ·
      refine ⟨34942718244454208239963123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46590290992605610986617497 34942718244454208239963123)
      ·
        refine ⟨52414077366681312359944685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34942718244454208239963123 52414077366681312359944685)
        ·
          refine ⟨19655279012505492134979257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52414077366681312359944685 19655279012505492134979257)
          ·
            refine ⟨14741459259379119101234443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19655279012505492134979257 14741459259379119101234443)
            ·
              refine ⟨22112188889068678651851665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14741459259379119101234443 22112188889068678651851665)
              ·
                refine ⟨16584141666801508988888749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22112188889068678651851665 16584141666801508988888749)
                ·
                  refine ⟨6219053125050565870833281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16584141666801508988888749 6219053125050565870833281)
                  ·
                    refine ⟨4664289843787924403124961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6219053125050565870833281 4664289843787924403124961)
                    ·
                      refine ⟨3498217382840943302343721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664289843787924403124961 3498217382840943302343721)
                      ·
                        rfl

theorem cell23_6812754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_6812754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812754 prefixEnd_6812754 := by exact prefixLift 6812754
  have htrace : WordTrace (prefixWord ++ tailWord_6812754) baseStart_6812754 baseEnd_6812754 := by
    simpa [prefixWord, tailWord_6812754, baseEnd_6812754] using wordTrace_append hprefix tailTrace_6812754
  have hstable : (prefixWord ++ tailWord_6812754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812754).length < 2 ^ (prefixWord ++ tailWord_6812754).sum := by decide
  have hdescent : baseEnd_6812754 < baseStart_6812754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812758 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 2, 3, 2]
def baseStart_6812758 : Nat := 118140960795 + 6812758 * 2 ^ 59
def prefixEnd_6812758 : Nat := 4983230072969 + 3 ^ 40 * 6812758 * 2
def baseEnd_6812758 : Nat := 3498219436763561286693703

theorem tailTrace_6812758 : CollatzResearch.WordTrace tailWord_6812758 prefixEnd_6812758 3498219436763561286693703 := by
  unfold tailWord_6812758
  simp only [CollatzResearch.WordTrace]
  refine ⟨15530106115784297954902433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165654465235032511518959285 15530106115784297954902433)
  ·
    refine ⟨11647579586838223466176825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15530106115784297954902433 11647579586838223466176825)
    ·
      refine ⟨8735684690128667599632619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11647579586838223466176825 8735684690128667599632619)
      ·
        refine ⟨13103527035193001399448929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735684690128667599632619 13103527035193001399448929)
        ·
          refine ⟨9827645276394751049586697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13103527035193001399448929 9827645276394751049586697)
          ·
            refine ⟨7370733957296063287190023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9827645276394751049586697 7370733957296063287190023)
            ·
              refine ⟨11056100935944094930785035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7370733957296063287190023 11056100935944094930785035)
              ·
                refine ⟨16584151403916142396177553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056100935944094930785035 16584151403916142396177553)
                ·
                  refine ⟨12438113552937106797133165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16584151403916142396177553 12438113552937106797133165)
                  ·
                    refine ⟨4664292582351415048924937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12438113552937106797133165 4664292582351415048924937)
                    ·
                      refine ⟨3498219436763561286693703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664292582351415048924937 3498219436763561286693703)
                      ·
                        rfl

theorem cell23_6812758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_6812758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812758 prefixEnd_6812758 := by exact prefixLift 6812758
  have htrace : WordTrace (prefixWord ++ tailWord_6812758) baseStart_6812758 baseEnd_6812758 := by
    simpa [prefixWord, tailWord_6812758, baseEnd_6812758] using wordTrace_append hprefix tailTrace_6812758
  have hstable : (prefixWord ++ tailWord_6812758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812758).length < 2 ^ (prefixWord ++ tailWord_6812758).sum := by decide
  have hdescent : baseEnd_6812758 < baseStart_6812758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812798 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6812798 : Nat := 118140960795 + 6812798 * 2 ^ 59
def prefixEnd_6812798 : Nat := 4983230072969 + 3 ^ 40 * 6812798 * 2
def baseEnd_6812798 : Nat := 1166079991996580376731173

theorem tailTrace_6812798 : CollatzResearch.WordTrace tailWord_6812798 prefixEnd_6812798 1166079991996580376731173 := by
  unfold tailWord_6812798
  simp only [CollatzResearch.WordTrace]
  refine ⟨31060394596550481763736881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165655437848269236073263365 31060394596550481763736881)
  ·
    refine ⟨23295295947412861322802661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31060394596550481763736881 23295295947412861322802661)
    ·
      refine ⟨4367867990139911498025499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23295295947412861322802661 4367867990139911498025499)
      ·
        refine ⟨6551801985209867247038249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367867990139911498025499 6551801985209867247038249)
        ·
          refine ⟨4913851488907400435278687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6551801985209867247038249 4913851488907400435278687)
          ·
            refine ⟨7370777233361100652918031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4913851488907400435278687 7370777233361100652918031)
            ·
              refine ⟨11056165850041650979377047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7370777233361100652918031 11056165850041650979377047)
              ·
                refine ⟨16584248775062476469065571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056165850041650979377047 16584248775062476469065571)
                ·
                  refine ⟨24876373162593714703598357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16584248775062476469065571 24876373162593714703598357)
                  ·
                    refine ⟨1166079991996580376731173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24876373162593714703598357 1166079991996580376731173)
                    ·
                      rfl

theorem cell23_6812798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6812798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812798 prefixEnd_6812798 := by exact prefixLift 6812798
  have htrace : WordTrace (prefixWord ++ tailWord_6812798) baseStart_6812798 baseEnd_6812798 := by
    simpa [prefixWord, tailWord_6812798, baseEnd_6812798] using wordTrace_append hprefix tailTrace_6812798
  have hstable : (prefixWord ++ tailWord_6812798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812798).length < 2 ^ (prefixWord ++ tailWord_6812798).sum := by decide
  have hdescent : baseEnd_6812798 < baseStart_6812798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812803 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 2, 6]
def baseStart_6812803 : Nat := 118140960795 + 6812803 * 2 ^ 59
def prefixEnd_6812803 : Nat := 4983230072969 + 3 ^ 40 * 6812803 * 2
def baseEnd_6812803 : Nat := 1166080847797671203543665

theorem tailTrace_6812803 : CollatzResearch.WordTrace tailWord_6812803 prefixEnd_6812803 1166080847797671203543665 := by
  unfold tailWord_6812803
  simp only [CollatzResearch.WordTrace]
  refine ⟨248483339137385739963827063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165655559424923826642551375 248483339137385739963827063)
  ·
    refine ⟨372725008706078609945740595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248483339137385739963827063 372725008706078609945740595)
    ·
      refine ⟨559087513059117914918610893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372725008706078609945740595 559087513059117914918610893)
      ·
        refine ⟨209657817397169218094479085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559087513059117914918610893 209657817397169218094479085)
        ·
          refine ⟨78621681523938456785429657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209657817397169218094479085 78621681523938456785429657)
          ·
            refine ⟨58966261142953842589072243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78621681523938456785429657 58966261142953842589072243)
            ·
              refine ⟨88449391714430763883608365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58966261142953842589072243 88449391714430763883608365)
              ·
                refine ⟨33168521892911536456353137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88449391714430763883608365 33168521892911536456353137)
                ·
                  refine ⟨24876391419683652342264853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33168521892911536456353137 24876391419683652342264853)
                  ·
                    refine ⟨1166080847797671203543665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24876391419683652342264853 1166080847797671203543665)
                    ·
                      rfl

theorem cell23_6812803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 6].length) (baseStart_6812803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812803 prefixEnd_6812803 := by exact prefixLift 6812803
  have htrace : WordTrace (prefixWord ++ tailWord_6812803) baseStart_6812803 baseEnd_6812803 := by
    simpa [prefixWord, tailWord_6812803, baseEnd_6812803] using wordTrace_append hprefix tailTrace_6812803
  have hstable : (prefixWord ++ tailWord_6812803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812803).length < 2 ^ (prefixWord ++ tailWord_6812803).sum := by decide
  have hdescent : baseEnd_6812803 < baseStart_6812803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812814 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6812814 : Nat := 118140960795 + 6812814 * 2 ^ 59
def prefixEnd_6812814 : Nat := 4983230072969 + 3 ^ 40 * 6812814 * 2
def baseEnd_6812814 : Nat := 3498248191680213067593445

theorem tailTrace_6812814 : CollatzResearch.WordTrace tailWord_6812814 prefixEnd_6812814 3498248191680213067593445 := by
  unfold tailWord_6812814
  simp only [CollatzResearch.WordTrace]
  refine ⟨31060467542543236105309687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165655826893563925894984997 31060467542543236105309687)
  ·
    refine ⟨46590701313814854157964531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31060467542543236105309687 46590701313814854157964531)
    ·
      refine ⟨69886051970722281236946797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46590701313814854157964531 69886051970722281236946797)
      ·
        refine ⟨26207269489020855463855049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69886051970722281236946797 26207269489020855463855049)
        ·
          refine ⟨19655452116765641597891287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26207269489020855463855049 19655452116765641597891287)
          ·
            refine ⟨29483178175148462396836931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19655452116765641597891287 29483178175148462396836931)
            ·
              refine ⟨44224767262722693595255397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29483178175148462396836931 44224767262722693595255397)
              ·
                refine ⟨8292143861760505049110387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44224767262722693595255397 8292143861760505049110387)
                ·
                  refine ⟨12438215792640757573665581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8292143861760505049110387 12438215792640757573665581)
                  ·
                    refine ⟨4664330922240284090124593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12438215792640757573665581 4664330922240284090124593)
                    ·
                      refine ⟨3498248191680213067593445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664330922240284090124593 3498248191680213067593445)
                      ·
                        rfl

theorem cell23_6812814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6812814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812814 prefixEnd_6812814 := by exact prefixLift 6812814
  have htrace : WordTrace (prefixWord ++ tailWord_6812814) baseStart_6812814 baseEnd_6812814 := by
    simpa [prefixWord, tailWord_6812814, baseEnd_6812814] using wordTrace_append hprefix tailTrace_6812814
  have hstable : (prefixWord ++ tailWord_6812814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812814).length < 2 ^ (prefixWord ++ tailWord_6812814).sum := by decide
  have hdescent : baseEnd_6812814 < baseStart_6812814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812850 : List Nat := [3, 2, 1, 1, 1, 4, 3, 1, 7]
def baseStart_6812850 : Nat := 118140960795 + 6812850 * 2 ^ 59
def prefixEnd_6812850 : Nat := 4983230072969 + 3 ^ 40 * 6812850 * 2
def baseEnd_6812850 : Nat := 388696297442641658527031

theorem tailTrace_6812850 : CollatzResearch.WordTrace tailWord_6812850 prefixEnd_6812850 388696297442641658527031 := by
  unfold tailWord_6812850
  simp only [CollatzResearch.WordTrace]
  refine ⟨62121263342053866747697001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165656702245476977993858669 62121263342053866747697001)
  ·
    refine ⟨46590947506540400060772751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62121263342053866747697001 46590947506540400060772751)
    ·
      refine ⟨69886421259810600091159127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46590947506540400060772751 69886421259810600091159127)
      ·
        refine ⟨104829631889715900136738691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69886421259810600091159127 104829631889715900136738691)
        ·
          refine ⟨157244447834573850205108037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104829631889715900136738691 157244447834573850205108037)
          ·
            refine ⟨29483333968982596913457757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157244447834573850205108037 29483333968982596913457757)
            ·
              refine ⟨11056250238368473842546659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29483333968982596913457757 11056250238368473842546659)
              ·
                refine ⟨16584375357552710763819989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056250238368473842546659 16584375357552710763819989)
                ·
                  refine ⟨388696297442641658527031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16584375357552710763819989 388696297442641658527031)
                  ·
                    rfl

theorem cell23_6812850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_6812850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812850 prefixEnd_6812850 := by exact prefixLift 6812850
  have htrace : WordTrace (prefixWord ++ tailWord_6812850) baseStart_6812850 baseEnd_6812850 := by
    simpa [prefixWord, tailWord_6812850, baseEnd_6812850] using wordTrace_append hprefix tailTrace_6812850
  have hstable : (prefixWord ++ tailWord_6812850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812850).length < 2 ^ (prefixWord ++ tailWord_6812850).sum := by decide
  have hdescent : baseEnd_6812850 < baseStart_6812850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812861 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 2, 2, 2]
def baseStart_6812861 : Nat := 118140960795 + 6812861 * 2 ^ 59
def prefixEnd_6812861 : Nat := 4983230072969 + 3 ^ 40 * 6812861 * 2
def baseEnd_6812861 : Nat := 3498272325270974383705729

theorem tailTrace_6812861 : CollatzResearch.WordTrace tailWord_6812861 prefixEnd_6812861 3498272325270974383705729 := by
  unfold tailWord_6812861
  simp only [CollatzResearch.WordTrace]
  refine ⟨248485454571175615869438437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165656969714117077246292291 248485454571175615869438437)
  ·
    refine ⟨46591022732095427975519707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248485454571175615869438437 46591022732095427975519707)
    ·
      refine ⟨69886534098143141963279561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46591022732095427975519707 69886534098143141963279561)
      ·
        refine ⟨52414900573607356472459671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69886534098143141963279561 52414900573607356472459671)
        ·
          refine ⟨78622350860411034708689507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52414900573607356472459671 78622350860411034708689507)
          ·
            refine ⟨117933526290616552063034261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78622350860411034708689507 117933526290616552063034261)
            ·
              refine ⟨5528134044872650877954731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117933526290616552063034261 5528134044872650877954731)
              ·
                refine ⟨8292201067308976316932097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528134044872650877954731 8292201067308976316932097)
                ·
                  refine ⟨6219150800481732237699073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8292201067308976316932097 6219150800481732237699073)
                  ·
                    refine ⟨4664363100361299178274305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6219150800481732237699073 4664363100361299178274305)
                    ·
                      refine ⟨3498272325270974383705729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664363100361299178274305 3498272325270974383705729)
                      ·
                        rfl

theorem cell23_6812861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_6812861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812861 prefixEnd_6812861 := by exact prefixLift 6812861
  have htrace : WordTrace (prefixWord ++ tailWord_6812861) baseStart_6812861 baseEnd_6812861 := by
    simpa [prefixWord, tailWord_6812861, baseEnd_6812861] using wordTrace_append hprefix tailTrace_6812861
  have hstable : (prefixWord ++ tailWord_6812861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812861).length < 2 ^ (prefixWord ++ tailWord_6812861).sum := by decide
  have hdescent : baseEnd_6812861 < baseStart_6812861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812863 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 3, 7]
def baseStart_6812863 : Nat := 118140960795 + 6812863 * 2 ^ 59
def prefixEnd_6812863 : Nat := 4983230072969 + 3 ^ 40 * 6812863 * 2
def baseEnd_6812863 : Nat := 1166091117410761125293573

theorem tailTrace_6812863 : CollatzResearch.WordTrace tailWord_6812863 prefixEnd_6812863 1166091117410761125293573 := by
  unfold tailWord_6812863
  simp only [CollatzResearch.WordTrace]
  refine ⟨248485527517168370211011243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165657018344778913474007495 248485527517168370211011243)
  ·
    refine ⟨372728291275752555316516865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248485527517168370211011243 372728291275752555316516865)
    ·
      refine ⟨279546218456814416487387649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372728291275752555316516865 279546218456814416487387649)
      ·
        refine ⟨209659663842610812365540737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279546218456814416487387649 209659663842610812365540737)
        ·
          refine ⟨157244747881958109274155553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209659663842610812365540737 157244747881958109274155553)
          ·
            refine ⟨117933560911468581955616665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157244747881958109274155553 117933560911468581955616665)
            ·
              refine ⟨88450170683601436466712499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117933560911468581955616665 88450170683601436466712499)
              ·
                refine ⟨132675256025402154700068749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88450170683601436466712499 132675256025402154700068749)
                ·
                  refine ⟨49753221009525808012525781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132675256025402154700068749 49753221009525808012525781)
                  ·
                    refine ⟨1166091117410761125293573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49753221009525808012525781 1166091117410761125293573)
                    ·
                      rfl

theorem cell23_6812863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_6812863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812863 prefixEnd_6812863 := by exact prefixLift 6812863
  have htrace : WordTrace (prefixWord ++ tailWord_6812863) baseStart_6812863 baseEnd_6812863 := by
    simpa [prefixWord, tailWord_6812863, baseEnd_6812863] using wordTrace_append hprefix tailTrace_6812863
  have hstable : (prefixWord ++ tailWord_6812863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812863).length < 2 ^ (prefixWord ++ tailWord_6812863).sum := by decide
  have hdescent : baseEnd_6812863 < baseStart_6812863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812901 : List Nat := [1, 3, 1, 4, 3, 2, 2, 2, 5]
def baseStart_6812901 : Nat := 118140960795 + 6812901 * 2 ^ 59
def prefixEnd_6812901 : Nat := 4983230072969 + 3 ^ 40 * 6812901 * 2
def baseEnd_6812901 : Nat := 388699207166350469689505

theorem tailTrace_6812901 : CollatzResearch.WordTrace tailWord_6812901 prefixEnd_6812901 388699207166350469689505 := by
  unfold tailWord_6812901
  simp only [CollatzResearch.WordTrace]
  refine ⟨248486913491030702700894557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165657942327353801800596371 248486913491030702700894557)
  ·
    refine ⟨93182592559136513512835459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248486913491030702700894557 93182592559136513512835459)
    ·
      refine ⟨139773888838704770269253189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93182592559136513512835459 139773888838704770269253189)
      ·
        refine ⟨26207604157257144425484973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139773888838704770269253189 26207604157257144425484973)
        ·
          refine ⟨9827851558971429159556865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26207604157257144425484973 9827851558971429159556865)
          ·
            refine ⟨7370888669228571869667649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9827851558971429159556865 7370888669228571869667649)
            ·
              refine ⟨5528166501921428902250737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7370888669228571869667649 5528166501921428902250737)
              ·
                refine ⟨4146124876441071676688053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528166501921428902250737 4146124876441071676688053)
                ·
                  refine ⟨388699207166350469689505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4146124876441071676688053 388699207166350469689505)
                  ·
                    rfl

theorem cell23_6812901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 2, 5].length) (baseStart_6812901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812901 prefixEnd_6812901 := by exact prefixLift 6812901
  have htrace : WordTrace (prefixWord ++ tailWord_6812901) baseStart_6812901 baseEnd_6812901 := by
    simpa [prefixWord, tailWord_6812901, baseEnd_6812901] using wordTrace_append hprefix tailTrace_6812901
  have hstable : (prefixWord ++ tailWord_6812901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812901).length < 2 ^ (prefixWord ++ tailWord_6812901).sum := by decide
  have hdescent : baseEnd_6812901 < baseStart_6812901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812927 : List Nat := [1, 1, 2, 2, 1, 6, 1, 2, 3, 4]
def baseStart_6812927 : Nat := 118140960795 + 6812927 * 2 ^ 59
def prefixEnd_6812927 : Nat := 4983230072969 + 3 ^ 40 * 6812927 * 2
def baseEnd_6812927 : Nat := 1166102071664723708493475

theorem tailTrace_6812927 : CollatzResearch.WordTrace tailWord_6812927 prefixEnd_6812927 1166102071664723708493475 := by
  unfold tailWord_6812927
  simp only [CollatzResearch.WordTrace]
  refine ⟨248487861788936509141341035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165658574525957672760894023 248487861788936509141341035)
  ·
    refine ⟨372731792683404763712011553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248487861788936509141341035 372731792683404763712011553)
    ·
      refine ⟨279548844512553572784008665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372731792683404763712011553 279548844512553572784008665)
      ·
        refine ⟨209661633384415179588006499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279548844512553572784008665 209661633384415179588006499)
        ·
          refine ⟨314492450076622769382009749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209661633384415179588006499 314492450076622769382009749)
          ·
            refine ⟨14741833597341692314781707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314492450076622769382009749 14741833597341692314781707)
            ·
              refine ⟨22112750396012538472172561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14741833597341692314781707 22112750396012538472172561)
              ·
                refine ⟨16584562797009403854129421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22112750396012538472172561 16584562797009403854129421)
                ·
                  refine ⟨6219211048878526445298533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16584562797009403854129421 6219211048878526445298533)
                  ·
                    refine ⟨1166102071664723708493475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219211048878526445298533 1166102071664723708493475)
                    ·
                      rfl

theorem cell23_6812927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 4].length) (baseStart_6812927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812927 prefixEnd_6812927 := by exact prefixLift 6812927
  have htrace : WordTrace (prefixWord ++ tailWord_6812927) baseStart_6812927 baseEnd_6812927 := by
    simpa [prefixWord, tailWord_6812927, baseEnd_6812927] using wordTrace_append hprefix tailTrace_6812927
  have hstable : (prefixWord ++ tailWord_6812927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812927).length < 2 ^ (prefixWord ++ tailWord_6812927).sum := by decide
  have hdescent : baseEnd_6812927 < baseStart_6812927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6812957 : List Nat := [1, 4, 2, 3, 1, 2, 1, 1, 8]
def baseStart_6812957 : Nat := 118140960795 + 6812957 * 2 ^ 59
def prefixEnd_6812957 : Nat := 4983230072969 + 3 ^ 40 * 6812957 * 2
def baseEnd_6812957 : Nat := 388702402157089556456143

theorem tailTrace_6812957 : CollatzResearch.WordTrace tailWord_6812957 prefixEnd_6812957 388702402157089556456143 := by
  unfold tailWord_6812957
  simp only [CollatzResearch.WordTrace]
  refine ⟨248488955978827824264933125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165659303985885216176622083 248488955978827824264933125)
  ·
    refine ⟨46591679246030217049674961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248488955978827824264933125 46591679246030217049674961)
    ·
      refine ⟨34943759434522662787256221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46591679246030217049674961 34943759434522662787256221)
      ·
        refine ⟨13103909787945998545221083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34943759434522662787256221 13103909787945998545221083)
        ·
          refine ⟨19655864681918997817831625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13103909787945998545221083 19655864681918997817831625)
          ·
            refine ⟨14741898511439248363373719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19655864681918997817831625 14741898511439248363373719)
            ·
              refine ⟨22112847767158872545060579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14741898511439248363373719 22112847767158872545060579)
              ·
                refine ⟨33169271650738308817590869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22112847767158872545060579 33169271650738308817590869)
                ·
                  refine ⟨388702402157089556456143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33169271650738308817590869 388702402157089556456143)
                  ·
                    rfl

theorem cell23_6812957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_6812957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6812957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6812957 prefixEnd_6812957 := by exact prefixLift 6812957
  have htrace : WordTrace (prefixWord ++ tailWord_6812957) baseStart_6812957 baseEnd_6812957 := by
    simpa [prefixWord, tailWord_6812957, baseEnd_6812957] using wordTrace_append hprefix tailTrace_6812957
  have hstable : (prefixWord ++ tailWord_6812957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6812957).length < 2 ^ (prefixWord ++ tailWord_6812957).sum := by decide
  have hdescent : baseEnd_6812957 < baseStart_6812957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6812957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813000 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 3, 6]
def baseStart_6813000 : Nat := 118140960795 + 6813000 * 2 ^ 59
def prefixEnd_6813000 : Nat := 4983230072969 + 3 ^ 40 * 6813000 * 2
def baseEnd_6813000 : Nat := 1166114566360649779955863

theorem tailTrace_6813000 : CollatzResearch.WordTrace tailWord_6813000 prefixEnd_6813000 1166114566360649779955863 := by
  unfold tailWord_6813000
  simp only [CollatzResearch.WordTrace]
  refine ⟨124245262158836021304374227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165660349545114695072498969 124245262158836021304374227)
  ·
    refine ⟨186367893238254031956561341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124245262158836021304374227 186367893238254031956561341)
    ·
      refine ⟨69887959964345261983710503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186367893238254031956561341 69887959964345261983710503)
      ·
        refine ⟨104831939946517892975565755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69887959964345261983710503 104831939946517892975565755)
        ·
          refine ⟨157247909919776839463348633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104831939946517892975565755 157247909919776839463348633)
          ·
            refine ⟨117935932439832629597511475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157247909919776839463348633 117935932439832629597511475)
            ·
              refine ⟨176903898659748944396267213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117935932439832629597511475 176903898659748944396267213)
              ·
                refine ⟨66338961997405854148600205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176903898659748944396267213 66338961997405854148600205)
                ·
                  refine ⟨24877110749027195305725077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66338961997405854148600205 24877110749027195305725077)
                  ·
                    refine ⟨1166114566360649779955863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24877110749027195305725077 1166114566360649779955863)
                    ·
                      rfl

theorem cell23_6813000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_6813000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813000 prefixEnd_6813000 := by exact prefixLift 6813000
  have htrace : WordTrace (prefixWord ++ tailWord_6813000) baseStart_6813000 baseEnd_6813000 := by
    simpa [prefixWord, tailWord_6813000, baseEnd_6813000] using wordTrace_append hprefix tailTrace_6813000
  have hstable : (prefixWord ++ tailWord_6813000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813000).length < 2 ^ (prefixWord ++ tailWord_6813000).sum := by decide
  have hdescent : baseEnd_6813000 < baseStart_6813000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813001 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 1, 1, 3]
def baseStart_6813001 : Nat := 118140960795 + 6813001 * 2 ^ 59
def prefixEnd_6813001 : Nat := 4983230072969 + 3 ^ 40 * 6813001 * 2
def baseEnd_6813001 : Nat := 3498344212562603835955085

theorem tailTrace_6813001 : CollatzResearch.WordTrace tailWord_6813001 prefixEnd_6813001 3498344212562603835955085 := by
  unfold tailWord_6813001
  simp only [CollatzResearch.WordTrace]
  refine ⟨248490560790668419779534857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165660373860445613186356571 248490560790668419779534857)
  ·
    refine ⟨186367920593001314834651143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248490560790668419779534857 186367920593001314834651143)
    ·
      refine ⟨279551880889501972251976715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186367920593001314834651143 279551880889501972251976715)
      ·
        refine ⟨419327821334252958377965073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279551880889501972251976715 419327821334252958377965073)
        ·
          refine ⟨314495866000689718783473805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419327821334252958377965073 314495866000689718783473805)
          ·
            refine ⟨117935949750258644543802677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314495866000689718783473805 117935949750258644543802677)
            ·
              refine ⟨11056495289086747925981501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117935949750258644543802677 11056495289086747925981501)
              ·
                refine ⟨4146185733407530472243063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11056495289086747925981501 4146185733407530472243063)
                ·
                  refine ⟨6219278600111295708364595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146185733407530472243063 6219278600111295708364595)
                  ·
                    refine ⟨9328917900166943562546893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219278600111295708364595 9328917900166943562546893)
                    ·
                      refine ⟨3498344212562603835955085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9328917900166943562546893 3498344212562603835955085)
                      ·
                        rfl

theorem cell23_6813001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 1, 3].length) (baseStart_6813001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813001 prefixEnd_6813001 := by exact prefixLift 6813001
  have htrace : WordTrace (prefixWord ++ tailWord_6813001) baseStart_6813001 baseEnd_6813001 := by
    simpa [prefixWord, tailWord_6813001, baseEnd_6813001] using wordTrace_append hprefix tailTrace_6813001
  have hstable : (prefixWord ++ tailWord_6813001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813001).length < 2 ^ (prefixWord ++ tailWord_6813001).sum := by decide
  have hdescent : baseEnd_6813001 < baseStart_6813001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813017 : List Nat := [1, 2, 1, 2, 2, 2, 4, 1, 4, 4]
def baseStart_6813017 : Nat := 118140960795 + 6813017 * 2 ^ 59
def prefixEnd_6813017 : Nat := 4983230072969 + 3 ^ 40 * 6813017 * 2
def baseEnd_6813017 : Nat := 1166117476084358591118337

theorem tailTrace_6813017 : CollatzResearch.WordTrace tailWord_6813017 prefixEnd_6813017 1166117476084358591118337 := by
  unfold tailWord_6813017
  simp only [CollatzResearch.WordTrace]
  refine ⟨248491144358610454512117305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165660762905740303008078203 248491144358610454512117305)
  ·
    refine ⟨186368358268957840884087979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248491144358610454512117305 186368358268957840884087979)
    ·
      refine ⟨279552537403436761326131969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186368358268957840884087979 279552537403436761326131969)
      ·
        refine ⟨209664403052577570994598977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279552537403436761326131969 209664403052577570994598977)
        ·
          refine ⟨157248302289433178245949233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209664403052577570994598977 157248302289433178245949233)
          ·
            refine ⟨117936226717074883684461925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157248302289433178245949233 117936226717074883684461925)
            ·
              refine ⟨22113042509451540690836611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117936226717074883684461925 22113042509451540690836611)
              ·
                refine ⟨33169563764177311036254917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22113042509451540690836611 33169563764177311036254917)
                ·
                  refine ⟨6219293205783245819297797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33169563764177311036254917 6219293205783245819297797)
                  ·
                    refine ⟨1166117476084358591118337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219293205783245819297797 1166117476084358591118337)
                    ·
                      rfl

theorem cell23_6813017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_6813017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813017 prefixEnd_6813017 := by exact prefixLift 6813017
  have htrace : WordTrace (prefixWord ++ tailWord_6813017) baseStart_6813017 baseEnd_6813017 := by
    simpa [prefixWord, tailWord_6813017, baseEnd_6813017] using wordTrace_append hprefix tailTrace_6813017
  have hstable : (prefixWord ++ tailWord_6813017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813017).length < 2 ^ (prefixWord ++ tailWord_6813017).sum := by decide
  have hdescent : baseEnd_6813017 < baseStart_6813017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813027 : List Nat := [1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5]
def baseStart_6813027 : Nat := 118140960795 + 6813027 * 2 ^ 59
def prefixEnd_6813027 : Nat := 4983230072969 + 3 ^ 40 * 6813027 * 2
def baseEnd_6813027 : Nat := 3498357563059620734229965

theorem tailTrace_6813027 : CollatzResearch.WordTrace tailWord_6813027 prefixEnd_6813027 3498357563059620734229965 := by
  unfold tailWord_6813027
  simp only [CollatzResearch.WordTrace]
  refine ⟨248491509088574226219981335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165661006059049484146654223 248491509088574226219981335)
  ·
    refine ⟨372737263632861339329972003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248491509088574226219981335 372737263632861339329972003)
    ·
      refine ⟨559105895449292008994958005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372737263632861339329972003 559105895449292008994958005)
      ·
        refine ⟨52416177698371125843277313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 559105895449292008994958005 52416177698371125843277313)
        ·
          refine ⟨39312133273778344382457985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52416177698371125843277313 39312133273778344382457985)
          ·
            refine ⟨29484099955333758286843489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39312133273778344382457985 29484099955333758286843489)
            ·
              refine ⟨22113074966500318715132617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29484099955333758286843489 22113074966500318715132617)
              ·
                refine ⟨16584806224875239036349463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22113074966500318715132617 16584806224875239036349463)
                ·
                  refine ⟨24877209337312858554524195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16584806224875239036349463 24877209337312858554524195)
                  ·
                    refine ⟨37315814005969287831786293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24877209337312858554524195 37315814005969287831786293)
                    ·
                      refine ⟨3498357563059620734229965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37315814005969287831786293 3498357563059620734229965)
                      ·
                        rfl

theorem cell23_6813027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_6813027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813027 prefixEnd_6813027 := by exact prefixLift 6813027
  have htrace : WordTrace (prefixWord ++ tailWord_6813027) baseStart_6813027 baseEnd_6813027 := by
    simpa [prefixWord, tailWord_6813027, baseEnd_6813027] using wordTrace_append hprefix tailTrace_6813027
  have hstable : (prefixWord ++ tailWord_6813027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813027).length < 2 ^ (prefixWord ++ tailWord_6813027).sum := by decide
  have hdescent : baseEnd_6813027 < baseStart_6813027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813037 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 6]
def baseStart_6813037 : Nat := 118140960795 + 6813037 * 2 ^ 59
def prefixEnd_6813037 : Nat := 4983230072969 + 3 ^ 40 * 6813037 * 2
def baseEnd_6813037 : Nat := 3498362697866165695104919

theorem tailTrace_6813037 : CollatzResearch.WordTrace tailWord_6813037 prefixEnd_6813037 3498362697866165695104919 := by
  unfold tailWord_6813037
  simp only [CollatzResearch.WordTrace]
  refine ⟨248491873818537997927845365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165661249212358665285230243 248491873818537997927845365)
  ·
    refine ⟨23296113170487937305735503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248491873818537997927845365 23296113170487937305735503)
    ·
      refine ⟨34944169755731905958603255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23296113170487937305735503 34944169755731905958603255)
      ·
        refine ⟨52416254633597858937904883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34944169755731905958603255 52416254633597858937904883)
        ·
          refine ⟨78624381950396788406857325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52416254633597858937904883 78624381950396788406857325)
          ·
            refine ⟨29484143231398795652571497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78624381950396788406857325 29484143231398795652571497)
            ·
              refine ⟨22113107423549096739428623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29484143231398795652571497 22113107423549096739428623)
              ·
                refine ⟨33169661135323645109142935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22113107423549096739428623 33169661135323645109142935)
                ·
                  refine ⟨49754491702985467663714403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33169661135323645109142935 49754491702985467663714403)
                  ·
                    refine ⟨74631737554478201495571605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49754491702985467663714403 74631737554478201495571605)
                    ·
                      refine ⟨3498362697866165695104919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74631737554478201495571605 3498362697866165695104919)
                      ·
                        rfl

theorem cell23_6813037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_6813037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813037 prefixEnd_6813037 := by exact prefixLift 6813037
  have htrace : WordTrace (prefixWord ++ tailWord_6813037) baseStart_6813037 baseEnd_6813037 := by
    simpa [prefixWord, tailWord_6813037, baseEnd_6813037] using wordTrace_append hprefix tailTrace_6813037
  have hstable : (prefixWord ++ tailWord_6813037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813037).length < 2 ^ (prefixWord ++ tailWord_6813037).sum := by decide
  have hdescent : baseEnd_6813037 < baseStart_6813037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813038 : List Nat := [4, 1, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_6813038 : Nat := 118140960795 + 6813038 * 2 ^ 59
def prefixEnd_6813038 : Nat := 4983230072969 + 3 ^ 40 * 6813038 * 2
def baseEnd_6813038 : Nat := 1166121070448940063730805

theorem tailTrace_6813038 : CollatzResearch.WordTrace tailWord_6813038 prefixEnd_6813038 1166121070448940063730805 := by
  unfold tailWord_6813038
  simp only [CollatzResearch.WordTrace]
  refine ⟨31061488786441796887328971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165661273527689583399087845 31061488786441796887328971)
  ·
    refine ⟨46592233179662695330993457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31061488786441796887328971 46592233179662695330993457)
    ·
      refine ⟨34944174884747021498245093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46592233179662695330993457 34944174884747021498245093)
      ·
        refine ⟨6552032790890066530920955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34944174884747021498245093 6552032790890066530920955)
        ·
          refine ⟨9828049186335099796381433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552032790890066530920955 9828049186335099796381433)
          ·
            refine ⟨7371036889751324847286075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9828049186335099796381433 7371036889751324847286075)
            ·
              refine ⟨11056555334626987270929113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371036889751324847286075 11056555334626987270929113)
              ·
                refine ⟨8292416500970240453196835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11056555334626987270929113 8292416500970240453196835)
                ·
                  refine ⟨12438624751455360679795253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8292416500970240453196835 12438624751455360679795253)
                  ·
                    refine ⟨1166121070448940063730805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12438624751455360679795253 1166121070448940063730805)
                    ·
                      rfl

theorem cell23_6813038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_6813038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813038 prefixEnd_6813038 := by exact prefixLift 6813038
  have htrace : WordTrace (prefixWord ++ tailWord_6813038) baseStart_6813038 baseEnd_6813038 := by
    simpa [prefixWord, tailWord_6813038, baseEnd_6813038] using wordTrace_append hprefix tailTrace_6813038
  have hstable : (prefixWord ++ tailWord_6813038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813038).length < 2 ^ (prefixWord ++ tailWord_6813038).sum := by decide
  have hdescent : baseEnd_6813038 < baseStart_6813038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813050 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6]
def baseStart_6813050 : Nat := 118140960795 + 6813050 * 2 ^ 59
def prefixEnd_6813050 : Nat := 4983230072969 + 3 ^ 40 * 6813050 * 2
def baseEnd_6813050 : Nat := 3498369373114674144242359

theorem tailTrace_6813050 : CollatzResearch.WordTrace tailWord_6813050 prefixEnd_6813050 3498369373114674144242359 := by
  unfold tailWord_6813050
  simp only [CollatzResearch.WordTrace]
  refine ⟨62123086991872725287017151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165661565311660600765379069 62123086991872725287017151)
  ·
    refine ⟨93184630487809087930525727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62123086991872725287017151 93184630487809087930525727)
    ·
      refine ⟨139776945731713631895788591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93184630487809087930525727 139776945731713631895788591)
      ·
        refine ⟨209665418597570447843682887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139776945731713631895788591 209665418597570447843682887)
        ·
          refine ⟨314498127896355671765524331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209665418597570447843682887 314498127896355671765524331)
          ·
            refine ⟨471747191844533507648286497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314498127896355671765524331 471747191844533507648286497)
            ·
              refine ⟨353810393883400130736214873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 471747191844533507648286497 353810393883400130736214873)
              ·
                refine ⟨265357795412550098052161155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353810393883400130736214873 265357795412550098052161155)
                ·
                  refine ⟨398036693118825147078241733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265357795412550098052161155 398036693118825147078241733)
                  ·
                    refine ⟨74631879959779715077170325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 398036693118825147078241733 74631879959779715077170325)
                    ·
                      refine ⟨3498369373114674144242359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74631879959779715077170325 3498369373114674144242359)
                      ·
                        rfl

theorem cell23_6813050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_6813050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813050 prefixEnd_6813050 := by exact prefixLift 6813050
  have htrace : WordTrace (prefixWord ++ tailWord_6813050) baseStart_6813050 baseEnd_6813050 := by
    simpa [prefixWord, tailWord_6813050, baseEnd_6813050] using wordTrace_append hprefix tailTrace_6813050
  have hstable : (prefixWord ++ tailWord_6813050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813050).length < 2 ^ (prefixWord ++ tailWord_6813050).sum := by decide
  have hdescent : baseEnd_6813050 < baseStart_6813050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813117 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6813117 : Nat := 118140960795 + 6813117 * 2 ^ 59
def prefixEnd_6813117 : Nat := 4983230072969 + 3 ^ 40 * 6813117 * 2
def baseEnd_6813117 : Nat := 3498403776318525382104551

theorem tailTrace_6813117 : CollatzResearch.WordTrace tailWord_6813117 prefixEnd_6813117 3498403776318525382104551 := by
  unfold tailWord_6813117
  simp only [CollatzResearch.WordTrace]
  refine ⟨248494791658248171590757605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165663194438832114393838403 248494791658248171590757605)
  ·
    refine ⟨46592773435921532173267051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248494791658248171590757605 46592773435921532173267051)
    ·
      refine ⟨69889160153882298259900577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46592773435921532173267051 69889160153882298259900577)
      ·
        refine ⟨52416870115411723694925433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69889160153882298259900577 52416870115411723694925433)
        ·
          refine ⟨39312652586558792771194075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52416870115411723694925433 39312652586558792771194075)
          ·
            refine ⟨58968978879838189156791113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39312652586558792771194075 58968978879838189156791113)
            ·
              refine ⟨44226734159878641867593335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58968978879838189156791113 44226734159878641867593335)
              ·
                refine ⟨66340101239817962801390003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44226734159878641867593335 66340101239817962801390003)
                ·
                  refine ⟨99510151859726944202085005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66340101239817962801390003 99510151859726944202085005)
                  ·
                    refine ⟨37316306947397604075781877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99510151859726944202085005 37316306947397604075781877)
                    ·
                      refine ⟨3498403776318525382104551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37316306947397604075781877 3498403776318525382104551)
                      ·
                        rfl

theorem cell23_6813117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6813117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813117 prefixEnd_6813117 := by exact prefixLift 6813117
  have htrace : WordTrace (prefixWord ++ tailWord_6813117) baseStart_6813117 baseEnd_6813117 := by
    simpa [prefixWord, tailWord_6813117, baseEnd_6813117] using wordTrace_append hprefix tailTrace_6813117
  have hstable : (prefixWord ++ tailWord_6813117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813117).length < 2 ^ (prefixWord ++ tailWord_6813117).sum := by decide
  have hdescent : baseEnd_6813117 < baseStart_6813117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813124 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6813124 : Nat := 118140960795 + 6813124 * 2 ^ 59
def prefixEnd_6813124 : Nat := 4983230072969 + 3 ^ 40 * 6813124 * 2
def baseEnd_6813124 : Nat := 1166135790227702284905673

theorem tailTrace_6813124 : CollatzResearch.WordTrace tailWord_6813124 prefixEnd_6813124 1166135790227702284905673 := by
  unfold tailWord_6813124
  simp only [CollatzResearch.WordTrace]
  refine ⟨124247523484611405893131213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165663364646148541190841617 124247523484611405893131213)
  ·
    refine ⟨46592821306729277209924205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124247523484611405893131213 46592821306729277209924205)
    ·
      refine ⟨17472307990023478953721577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46592821306729277209924205 17472307990023478953721577)
      ·
        refine ⟨13104230992517609215291183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17472307990023478953721577 13104230992517609215291183)
        ·
          refine ⟨19656346488776413822936775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13104230992517609215291183 19656346488776413822936775)
          ·
            refine ⟨29484519733164620734405163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19656346488776413822936775 29484519733164620734405163)
            ·
              refine ⟨44226779599746931101607745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29484519733164620734405163 44226779599746931101607745)
              ·
                refine ⟨33170084699810198326205809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44226779599746931101607745 33170084699810198326205809)
                ·
                  refine ⟨24877563524857648744654357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33170084699810198326205809 24877563524857648744654357)
                  ·
                    refine ⟨1166135790227702284905673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24877563524857648744654357 1166135790227702284905673)
                    ·
                      rfl

theorem cell23_6813124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6813124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813124 prefixEnd_6813124 := by exact prefixLift 6813124
  have htrace : WordTrace (prefixWord ++ tailWord_6813124) baseStart_6813124 baseEnd_6813124 := by
    simpa [prefixWord, tailWord_6813124, baseEnd_6813124] using wordTrace_append hprefix tailTrace_6813124
  have hstable : (prefixWord ++ tailWord_6813124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813124).length < 2 ^ (prefixWord ++ tailWord_6813124).sum := by decide
  have hdescent : baseEnd_6813124 < baseStart_6813124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813127 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_6813127 : Nat := 118140960795 + 6813127 * 2 ^ 59
def prefixEnd_6813127 : Nat := 4983230072969 + 3 ^ 40 * 6813127 * 2
def baseEnd_6813127 : Nat := 3498408911125070342979505

theorem tailTrace_6813127 : CollatzResearch.WordTrace tailWord_6813127 prefixEnd_6813127 3498408911125070342979505 := by
  unfold tailWord_6813127
  simp only [CollatzResearch.WordTrace]
  refine ⟨248495156388211943298621635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165663437592141295532414423 248495156388211943298621635)
  ·
    refine ⟨372742734582317914947932453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248495156388211943298621635 372742734582317914947932453)
    ·
      refine ⟨69889262734184609052737335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372742734582317914947932453 69889262734184609052737335)
      ·
        refine ⟨104833894101276913579106003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69889262734184609052737335 104833894101276913579106003)
        ·
          refine ⟨157250841151915370368659005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104833894101276913579106003 157250841151915370368659005)
          ·
            refine ⟨58969065431968263888247127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157250841151915370368659005 58969065431968263888247127)
            ·
              refine ⟨88453598147952395832370691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58969065431968263888247127 88453598147952395832370691)
              ·
                refine ⟨132680397221928593748556037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88453598147952395832370691 132680397221928593748556037)
                ·
                  refine ⟨24877574479111611327854257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132680397221928593748556037 24877574479111611327854257)
                  ·
                    refine ⟨18658180859333708495890693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24877574479111611327854257 18658180859333708495890693)
                    ·
                      refine ⟨3498408911125070342979505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18658180859333708495890693 3498408911125070342979505)
                      ·
                        rfl

theorem cell23_6813127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_6813127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813127 prefixEnd_6813127 := by exact prefixLift 6813127
  have htrace : WordTrace (prefixWord ++ tailWord_6813127) baseStart_6813127 baseEnd_6813127 := by
    simpa [prefixWord, tailWord_6813127, baseEnd_6813127] using wordTrace_append hprefix tailTrace_6813127
  have hstable : (prefixWord ++ tailWord_6813127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813127).length < 2 ^ (prefixWord ++ tailWord_6813127).sum := by decide
  have hdescent : baseEnd_6813127 < baseStart_6813127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813167 : List Nat := [1, 1, 2, 1, 4, 1, 4, 1, 1, 7]
def baseStart_6813167 : Nat := 118140960795 + 6813167 * 2 ^ 59
def prefixEnd_6813167 : Nat := 4983230072969 + 3 ^ 40 * 6813167 * 2
def baseEnd_6813167 : Nat := 1166143150117083395493107

theorem tailTrace_6813167 : CollatzResearch.WordTrace tailWord_6813167 prefixEnd_6813167 1166143150117083395493107 := by
  unfold tailWord_6813167
  simp only [CollatzResearch.WordTrace]
  refine ⟨248496615308067030130077755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165664410205378020086718503 248496615308067030130077755)
  ·
    refine ⟨372744922962100545195116633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248496615308067030130077755 372744922962100545195116633)
    ·
      refine ⟨279558692221575408896337475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372744922962100545195116633 279558692221575408896337475)
      ·
        refine ⟨419338038332363113344506213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279558692221575408896337475 419338038332363113344506213)
        ·
          refine ⟨78625882187318083752094915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419338038332363113344506213 78625882187318083752094915)
          ·
            refine ⟨117938823280977125628142373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78625882187318083752094915 117938823280977125628142373)
            ·
              refine ⟨22113529365183211055276695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117938823280977125628142373 22113529365183211055276695)
              ·
                refine ⟨33170294047774816582915043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22113529365183211055276695 33170294047774816582915043)
                ·
                  refine ⟨49755441071662224874372565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33170294047774816582915043 49755441071662224874372565)
                  ·
                    refine ⟨1166143150117083395493107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49755441071662224874372565 1166143150117083395493107)
                    ·
                      rfl

theorem cell23_6813167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_6813167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813167 prefixEnd_6813167 := by exact prefixLift 6813167
  have htrace : WordTrace (prefixWord ++ tailWord_6813167) baseStart_6813167 baseEnd_6813167 := by
    simpa [prefixWord, tailWord_6813167, baseEnd_6813167] using wordTrace_append hprefix tailTrace_6813167
  have hstable : (prefixWord ++ tailWord_6813167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813167).length < 2 ^ (prefixWord ++ tailWord_6813167).sum := by decide
  have hdescent : baseEnd_6813167 < baseStart_6813167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813177 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6813177 : Nat := 118140960795 + 6813177 * 2 ^ 59
def prefixEnd_6813177 : Nat := 4983230072969 + 3 ^ 40 * 6813177 * 2
def baseEnd_6813177 : Nat := 3498434585157795147354275

theorem tailTrace_6813177 : CollatzResearch.WordTrace tailWord_6813177 prefixEnd_6813177 3498434585157795147354275 := by
  unfold tailWord_6813177
  simp only [CollatzResearch.WordTrace]
  refine ⟨248496980038030801837941785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165664653358687201225294523 248496980038030801837941785)
  ·
    refine ⟨186372735028523101378456339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248496980038030801837941785 186372735028523101378456339)
    ·
      refine ⟨279559102542784652067684509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186372735028523101378456339 279559102542784652067684509)
      ·
        refine ⟨104834663453544244525381691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279559102542784652067684509 104834663453544244525381691)
        ·
          refine ⟨157251995180316366788072537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104834663453544244525381691 157251995180316366788072537)
          ·
            refine ⟨117938996385237275091054403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157251995180316366788072537 117938996385237275091054403)
            ·
              refine ⟨176908494577855912636581605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117938996385237275091054403 176908494577855912636581605)
              ·
                refine ⟨33170342733347983619359051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176908494577855912636581605 33170342733347983619359051)
                ·
                  refine ⟨49755514100021975429038577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33170342733347983619359051 49755514100021975429038577)
                  ·
                    refine ⟨37316635575016481571778933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49755514100021975429038577 37316635575016481571778933)
                    ·
                      refine ⟨3498434585157795147354275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37316635575016481571778933 3498434585157795147354275)
                      ·
                        rfl

theorem cell23_6813177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6813177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813177 prefixEnd_6813177 := by exact prefixLift 6813177
  have htrace : WordTrace (prefixWord ++ tailWord_6813177) baseStart_6813177 baseEnd_6813177 := by
    simpa [prefixWord, tailWord_6813177, baseEnd_6813177] using wordTrace_append hprefix tailTrace_6813177
  have hstable : (prefixWord ++ tailWord_6813177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813177).length < 2 ^ (prefixWord ++ tailWord_6813177).sum := by decide
  have hdescent : baseEnd_6813177 < baseStart_6813177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813187 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4]
def baseStart_6813187 : Nat := 118140960795 + 6813187 * 2 ^ 59
def prefixEnd_6813187 : Nat := 4983230072969 + 3 ^ 40 * 6813187 * 2
def baseEnd_6813187 : Nat := 3498439719964340108229229

theorem tailTrace_6813187 : CollatzResearch.WordTrace tailWord_6813187 prefixEnd_6813187 3498439719964340108229229 := by
  unfold tailWord_6813187
  simp only [CollatzResearch.WordTrace]
  refine ⟨248497344767994573545805815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165664896511996382363870543 248497344767994573545805815)
  ·
    refine ⟨372746017151991860318708723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248497344767994573545805815 372746017151991860318708723)
    ·
      refine ⟨559119025727987790478063085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372746017151991860318708723 559119025727987790478063085)
      ·
        refine ⟨209669634647995421429273657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559119025727987790478063085 209669634647995421429273657)
        ·
          refine ⟨157252225985996566071955243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209669634647995421429273657 157252225985996566071955243)
          ·
            refine ⟨235878338978994849107932865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157252225985996566071955243 235878338978994849107932865)
            ·
              refine ⟨176908754234246136830949649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235878338978994849107932865 176908754234246136830949649)
              ·
                refine ⟨132681565675684602623212237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176908754234246136830949649 132681565675684602623212237)
                ·
                  refine ⟨49755587128381725983704589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132681565675684602623212237 49755587128381725983704589)
                  ·
                    refine ⟨18658345173143147243889221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49755587128381725983704589 18658345173143147243889221)
                    ·
                      refine ⟨3498439719964340108229229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18658345173143147243889221 3498439719964340108229229)
                      ·
                        rfl

theorem cell23_6813187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_6813187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813187 prefixEnd_6813187 := by exact prefixLift 6813187
  have htrace : WordTrace (prefixWord ++ tailWord_6813187) baseStart_6813187 baseEnd_6813187 := by
    simpa [prefixWord, tailWord_6813187, baseEnd_6813187] using wordTrace_append hprefix tailTrace_6813187
  have hstable : (prefixWord ++ tailWord_6813187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813187).length < 2 ^ (prefixWord ++ tailWord_6813187).sum := by decide
  have hdescent : baseEnd_6813187 < baseStart_6813187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813188 : List Nat := [2, 3, 2, 3, 3, 1, 1, 1, 7]
def baseStart_6813188 : Nat := 118140960795 + 6813188 * 2 ^ 59
def prefixEnd_6813188 : Nat := 4983230072969 + 3 ^ 40 * 6813188 * 2
def baseEnd_6813188 : Nat := 388715581493888289368525

theorem tailTrace_6813188 : CollatzResearch.WordTrace tailWord_6813188 prefixEnd_6813188 388715581493888289368525 := by
  unfold tailWord_6813188
  simp only [CollatzResearch.WordTrace]
  refine ⟨124248690620495475358296109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165664920827327300477728145 124248690620495475358296109)
  ·
    refine ⟨46593258982685803259361041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124248690620495475358296109 46593258982685803259361041)
    ·
      refine ⟨34944944237014352444520781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46593258982685803259361041 34944944237014352444520781)
      ·
        refine ⟨13104354088880382166695293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34944944237014352444520781 13104354088880382166695293)
        ·
          refine ⟨4914132783330143312510735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13104354088880382166695293 4914132783330143312510735)
          ·
            refine ⟨7371199174995214968766103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914132783330143312510735 7371199174995214968766103)
            ·
              refine ⟨11056798762492822453149155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371199174995214968766103 11056798762492822453149155)
              ·
                refine ⟨16585198143739233679723733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11056798762492822453149155 16585198143739233679723733)
                ·
                  refine ⟨388715581493888289368525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16585198143739233679723733 388715581493888289368525)
                  ·
                    rfl

theorem cell23_6813188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_6813188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813188 prefixEnd_6813188 := by exact prefixLift 6813188
  have htrace : WordTrace (prefixWord ++ tailWord_6813188) baseStart_6813188 baseEnd_6813188 := by
    simpa [prefixWord, tailWord_6813188, baseEnd_6813188] using wordTrace_append hprefix tailTrace_6813188
  have hstable : (prefixWord ++ tailWord_6813188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813188).length < 2 ^ (prefixWord ++ tailWord_6813188).sum := by decide
  have hdescent : baseEnd_6813188 < baseStart_6813188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813194 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5]
def baseStart_6813194 : Nat := 118140960795 + 6813194 * 2 ^ 59
def prefixEnd_6813194 : Nat := 4983230072969 + 3 ^ 40 * 6813194 * 2
def baseEnd_6813194 : Nat := 3498443314328921580841697

theorem tailTrace_6813194 : CollatzResearch.WordTrace tailWord_6813194 prefixEnd_6813194 3498443314328921580841697 := by
  unfold tailWord_6813194
  simp only [CollatzResearch.WordTrace]
  refine ⟨62124400019742303435327659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165665066719312809160873757 62124400019742303435327659)
  ·
    refine ⟨93186600029613455152991489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62124400019742303435327659 93186600029613455152991489)
    ·
      refine ⟨69889950022210091364743617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93186600029613455152991489 69889950022210091364743617)
      ·
        refine ⟨52417462516657568523557713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69889950022210091364743617 52417462516657568523557713)
        ·
          refine ⟨39313096887493176392668285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52417462516657568523557713 39313096887493176392668285)
          ·
            refine ⟨14742411332809941147250607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39313096887493176392668285 14742411332809941147250607)
            ·
              refine ⟨22113616999214911720875911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14742411332809941147250607 22113616999214911720875911)
              ·
                refine ⟨33170425498822367581313867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22113616999214911720875911 33170425498822367581313867)
                ·
                  refine ⟨49755638248233551371970801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33170425498822367581313867 49755638248233551371970801)
                  ·
                    refine ⟨37316728686175163528978101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49755638248233551371970801 37316728686175163528978101)
                    ·
                      refine ⟨3498443314328921580841697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37316728686175163528978101 3498443314328921580841697)
                      ·
                        rfl

theorem cell23_6813194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_6813194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813194 prefixEnd_6813194 := by exact prefixLift 6813194
  have htrace : WordTrace (prefixWord ++ tailWord_6813194) baseStart_6813194 baseEnd_6813194 := by
    simpa [prefixWord, tailWord_6813194, baseEnd_6813194] using wordTrace_append hprefix tailTrace_6813194
  have hstable : (prefixWord ++ tailWord_6813194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813194).length < 2 ^ (prefixWord ++ tailWord_6813194).sum := by decide
  have hdescent : baseEnd_6813194 < baseStart_6813194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813241 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6813241 : Nat := 118140960795 + 6813241 * 2 ^ 59
def prefixEnd_6813241 : Nat := 4983230072969 + 3 ^ 40 * 6813241 * 2
def baseEnd_6813241 : Nat := 3498467447919682896953981

theorem tailTrace_6813241 : CollatzResearch.WordTrace tailWord_6813241 prefixEnd_6813241 3498467447919682896953981 := by
  unfold tailWord_6813241
  simp only [CollatzResearch.WordTrace]
  refine ⟨248499314309798940768271577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165666209539865960512181051 248499314309798940768271577)
  ·
    refine ⟨186374485732349205576203683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248499314309798940768271577 186374485732349205576203683)
    ·
      refine ⟨279561728598523808364305525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186374485732349205576203683 279561728598523808364305525)
      ·
        refine ⟨26208912056111607034153643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279561728598523808364305525 26208912056111607034153643)
        ·
          refine ⟨39313368084167410551230465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26208912056111607034153643 39313368084167410551230465)
          ·
            refine ⟨29485026063125557913422849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39313368084167410551230465 29485026063125557913422849)
            ·
              refine ⟨22113769547344168435067137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29485026063125557913422849 22113769547344168435067137)
              ·
                refine ⟨16585327160508126326300353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22113769547344168435067137 16585327160508126326300353)
                ·
                  refine ⟨12438995370381094744725265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16585327160508126326300353 12438995370381094744725265)
                  ·
                    refine ⟨9329246527785821058543949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12438995370381094744725265 9329246527785821058543949)
                    ·
                      refine ⟨3498467447919682896953981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9329246527785821058543949 3498467447919682896953981)
                      ·
                        rfl

theorem cell23_6813241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6813241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813241 prefixEnd_6813241 := by exact prefixLift 6813241
  have htrace : WordTrace (prefixWord ++ tailWord_6813241) baseStart_6813241 baseEnd_6813241 := by
    simpa [prefixWord, tailWord_6813241, baseEnd_6813241] using wordTrace_append hprefix tailTrace_6813241
  have hstable : (prefixWord ++ tailWord_6813241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813241).length < 2 ^ (prefixWord ++ tailWord_6813241).sum := by decide
  have hdescent : baseEnd_6813241 < baseStart_6813241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813271 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 3]
def baseStart_6813271 : Nat := 118140960795 + 6813271 * 2 ^ 59
def prefixEnd_6813271 : Nat := 4983230072969 + 3 ^ 40 * 6813271 * 2
def baseEnd_6813271 : Nat := 3498482852339317779578843

theorem tailTrace_6813271 : CollatzResearch.WordTrace tailWord_6813271 prefixEnd_6813271 3498482852339317779578843 := by
  unfold tailWord_6813271
  simp only [CollatzResearch.WordTrace]
  refine ⟨248500408499690255891863667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165666938999793503927909111 248500408499690255891863667)
  ·
    refine ⟨372750612749535383837795501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248500408499690255891863667 372750612749535383837795501)
    ·
      refine ⟨139781479781075768939173313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372750612749535383837795501 139781479781075768939173313)
      ·
        refine ⟨104836109835806826704379985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139781479781075768939173313 104836109835806826704379985)
        ·
          refine ⟨78627082376855120028284989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104836109835806826704379985 78627082376855120028284989)
          ·
            refine ⟨29485155891320670010606871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78627082376855120028284989 29485155891320670010606871)
            ·
              refine ⟨44227733836981005015910307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29485155891320670010606871 44227733836981005015910307)
              ·
                refine ⟨66341600755471507523865461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44227733836981005015910307 66341600755471507523865461)
                ·
                  refine ⟨6219525070825453830362387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66341600755471507523865461 6219525070825453830362387)
                  ·
                    refine ⟨9329287606238180745543581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6219525070825453830362387 9329287606238180745543581)
                    ·
                      refine ⟨3498482852339317779578843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9329287606238180745543581 3498482852339317779578843)
                      ·
                        rfl

theorem cell23_6813271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_6813271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813271 prefixEnd_6813271 := by exact prefixLift 6813271
  have htrace : WordTrace (prefixWord ++ tailWord_6813271) baseStart_6813271 baseEnd_6813271 := by
    simpa [prefixWord, tailWord_6813271, baseEnd_6813271] using wordTrace_append hprefix tailTrace_6813271
  have hstable : (prefixWord ++ tailWord_6813271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813271).length < 2 ^ (prefixWord ++ tailWord_6813271).sum := by decide
  have hdescent : baseEnd_6813271 < baseStart_6813271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813281 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_6813281 : Nat := 118140960795 + 6813281 * 2 ^ 59
def prefixEnd_6813281 : Nat := 4983230072969 + 3 ^ 40 * 6813281 * 2
def baseEnd_6813281 : Nat := 3498487987145862740453797

theorem tailTrace_6813281 : CollatzResearch.WordTrace tailWord_6813281 prefixEnd_6813281 3498487987145862740453797 := by
  unfold tailWord_6813281
  simp only [CollatzResearch.WordTrace]
  refine ⟨248500773229654027599727697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165667182153102685066485131 248500773229654027599727697)
  ·
    refine ⟨186375579922240520699795773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248500773229654027599727697 186375579922240520699795773)
    ·
      refine ⟨69890842470840195262423415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186375579922240520699795773 69890842470840195262423415)
      ·
        refine ⟨104836263706260292893635123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69890842470840195262423415 104836263706260292893635123)
        ·
          refine ⟨157254395559390439340452685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104836263706260292893635123 157254395559390439340452685)
          ·
            refine ⟨58970398334771414752669757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157254395559390439340452685 58970398334771414752669757)
            ·
              refine ⟨22113899375539280532251159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58970398334771414752669757 22113899375539280532251159)
              ·
                refine ⟨33170849063308920798376739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22113899375539280532251159 33170849063308920798376739)
                ·
                  refine ⟨49756273594963381197565109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33170849063308920798376739 49756273594963381197565109)
                  ·
                    refine ⟨4664650649527816987271729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49756273594963381197565109 4664650649527816987271729)
                    ·
                      refine ⟨3498487987145862740453797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664650649527816987271729 3498487987145862740453797)
                      ·
                        rfl

theorem cell23_6813281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_6813281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813281 prefixEnd_6813281 := by exact prefixLift 6813281
  have htrace : WordTrace (prefixWord ++ tailWord_6813281) baseStart_6813281 baseEnd_6813281 := by
    simpa [prefixWord, tailWord_6813281, baseEnd_6813281] using wordTrace_append hprefix tailTrace_6813281
  have hstable : (prefixWord ++ tailWord_6813281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813281).length < 2 ^ (prefixWord ++ tailWord_6813281).sum := by decide
  have hdescent : baseEnd_6813281 < baseStart_6813281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813321 : List Nat := [1, 2, 1, 1, 4, 1, 2, 5, 2, 4]
def baseStart_6813321 : Nat := 118140960795 + 6813321 * 2 ^ 59
def prefixEnd_6813321 : Nat := 4983230072969 + 3 ^ 40 * 6813321 * 2
def baseEnd_6813321 : Nat := 1166169508790680861317871

theorem tailTrace_6813321 : CollatzResearch.WordTrace tailWord_6813321 prefixEnd_6813321 1166169508790680861317871 := by
  unfold tailWord_6813321
  simp only [CollatzResearch.WordTrace]
  refine ⟨248502232149509114431183817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165668154766339409620789211 248502232149509114431183817)
  ·
    refine ⟨186376674112131835823387863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248502232149509114431183817 186376674112131835823387863)
    ·
      refine ⟨279565011168197753735081795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186376674112131835823387863 279565011168197753735081795)
      ·
        refine ⟨419347516752296630602622693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279565011168197753735081795 419347516752296630602622693)
        ·
          refine ⟨78627659391055618237991755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 419347516752296630602622693 78627659391055618237991755)
          ·
            refine ⟨117941489086583427356987633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78627659391055618237991755 117941489086583427356987633)
            ·
              refine ⟨88456116814937570517740725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117941489086583427356987633 88456116814937570517740725)
              ·
                refine ⟨8292760951400397236038193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88456116814937570517740725 8292760951400397236038193)
                ·
                  refine ⟨6219570713550297927028645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8292760951400397236038193 6219570713550297927028645)
                  ·
                    refine ⟨1166169508790680861317871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219570713550297927028645 1166169508790680861317871)
                    ·
                      rfl

theorem cell23_6813321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_6813321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813321 prefixEnd_6813321 := by exact prefixLift 6813321
  have htrace : WordTrace (prefixWord ++ tailWord_6813321) baseStart_6813321 baseEnd_6813321 := by
    simpa [prefixWord, tailWord_6813321, baseEnd_6813321] using wordTrace_append hprefix tailTrace_6813321
  have hstable : (prefixWord ++ tailWord_6813321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813321).length < 2 ^ (prefixWord ++ tailWord_6813321).sum := by decide
  have hdescent : baseEnd_6813321 < baseStart_6813321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813324 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 1, 1, 6]
def baseStart_6813324 : Nat := 118140960795 + 6813324 * 2 ^ 59
def prefixEnd_6813324 : Nat := 4983230072969 + 3 ^ 40 * 6813324 * 2
def baseEnd_6813324 : Nat := 3498510066814006072216099

theorem tailTrace_6813324 : CollatzResearch.WordTrace tailWord_6813324 prefixEnd_6813324 3498510066814006072216099 := by
  unfold tailWord_6813324
  simp only [CollatzResearch.WordTrace]
  refine ⟨124251170784249122971771513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165668227712332163962362017 124251170784249122971771513)
  ·
    refine ⟨93188378088186842228828635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124251170784249122971771513 93188378088186842228828635)
    ·
      refine ⟨139782567132280263343242953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93188378088186842228828635 139782567132280263343242953)
      ·
        refine ⟨104836925349210197507432215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139782567132280263343242953 104836925349210197507432215)
        ·
          refine ⟨157255388023815296261148323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104836925349210197507432215 157255388023815296261148323)
          ·
            refine ⟨235883082035722944391722485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157255388023815296261148323 235883082035722944391722485)
            ·
              refine ⟨22114038940849026036723983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235883082035722944391722485 22114038940849026036723983)
              ·
                refine ⟨33171058411273539055085975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22114038940849026036723983 33171058411273539055085975)
                ·
                  refine ⟨49756587616910308582628963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33171058411273539055085975 49756587616910308582628963)
                  ·
                    refine ⟨74634881425365462873943445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49756587616910308582628963 74634881425365462873943445)
                    ·
                      refine ⟨3498510066814006072216099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74634881425365462873943445 3498510066814006072216099)
                      ·
                        rfl

theorem cell23_6813324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_6813324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813324 prefixEnd_6813324 := by exact prefixLift 6813324
  have htrace : WordTrace (prefixWord ++ tailWord_6813324) baseStart_6813324 baseEnd_6813324 := by
    simpa [prefixWord, tailWord_6813324, baseEnd_6813324] using wordTrace_append hprefix tailTrace_6813324
  have hstable : (prefixWord ++ tailWord_6813324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813324).length < 2 ^ (prefixWord ++ tailWord_6813324).sum := by decide
  have hdescent : baseEnd_6813324 < baseStart_6813324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813348 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_6813348 : Nat := 118140960795 + 6813348 * 2 ^ 59
def prefixEnd_6813348 : Nat := 4983230072969 + 3 ^ 40 * 6813348 * 2
def baseEnd_6813348 : Nat := 3498522390349713978315989

theorem tailTrace_6813348 : CollatzResearch.WordTrace tailWord_6813348 prefixEnd_6813348 3498522390349713978315989 := by
  unfold tailWord_6813348
  simp only [CollatzResearch.WordTrace]
  refine ⟨124251608460205649021208349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165668811280274198694944465 124251608460205649021208349)
  ·
    refine ⟨46594353172577118382953131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124251608460205649021208349 46594353172577118382953131)
    ·
      refine ⟨69891529758865677574429697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46594353172577118382953131 69891529758865677574429697)
      ·
        refine ⟨52418647319149258180822273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69891529758865677574429697 52418647319149258180822273)
        ·
          refine ⟨39313985489361943635616705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52418647319149258180822273 39313985489361943635616705)
          ·
            refine ⟨29485489117021457726712529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39313985489361943635616705 29485489117021457726712529)
            ·
              refine ⟨22114116837766093295034397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29485489117021457726712529 22114116837766093295034397)
              ·
                refine ⟨8292793814162284985637899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22114116837766093295034397 8292793814162284985637899)
                ·
                  refine ⟨12439190721243427478456849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8292793814162284985637899 12439190721243427478456849)
                  ·
                    refine ⟨9329393040932570608842637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12439190721243427478456849 9329393040932570608842637)
                    ·
                      refine ⟨3498522390349713978315989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9329393040932570608842637 3498522390349713978315989)
                      ·
                        rfl

theorem cell23_6813348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_6813348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813348 prefixEnd_6813348 := by exact prefixLift 6813348
  have htrace : WordTrace (prefixWord ++ tailWord_6813348) baseStart_6813348 baseEnd_6813348 := by
    simpa [prefixWord, tailWord_6813348, baseEnd_6813348] using wordTrace_append hprefix tailTrace_6813348
  have hstable : (prefixWord ++ tailWord_6813348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813348).length < 2 ^ (prefixWord ++ tailWord_6813348).sum := by decide
  have hdescent : baseEnd_6813348 < baseStart_6813348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813382 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_6813382 : Nat := 118140960795 + 6813382 * 2 ^ 59
def prefixEnd_6813382 : Nat := 4983230072969 + 3 ^ 40 * 6813382 * 2
def baseEnd_6813382 : Nat := 3498539848691966845290833

theorem tailTrace_6813382 : CollatzResearch.WordTrace tailWord_6813382 prefixEnd_6813382 3498539848691966845290833 := by
  unfold tailWord_6813382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7765764281321503807786075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165669638001525414566102933 7765764281321503807786075)
  ·
    refine ⟨11648646421982255711679113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7765764281321503807786075 11648646421982255711679113)
    ·
      refine ⟨8736484816486691783759335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11648646421982255711679113 8736484816486691783759335)
      ·
        refine ⟨13104727224730037675639003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8736484816486691783759335 13104727224730037675639003)
        ·
          refine ⟨19657090837095056513458505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13104727224730037675639003 19657090837095056513458505)
          ·
            refine ⟨14742818127821292385093879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19657090837095056513458505 14742818127821292385093879)
            ·
              refine ⟨22114227191731938577640819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14742818127821292385093879 22114227191731938577640819)
              ·
                refine ⟨33171340787597907866461229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22114227191731938577640819 33171340787597907866461229)
                ·
                  refine ⟨12439252795349215449922961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33171340787597907866461229 12439252795349215449922961)
                  ·
                    refine ⟨9329439596511911587442221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12439252795349215449922961 9329439596511911587442221)
                    ·
                      refine ⟨3498539848691966845290833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9329439596511911587442221 3498539848691966845290833)
                      ·
                        rfl

theorem cell23_6813382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_6813382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813382 prefixEnd_6813382 := by exact prefixLift 6813382
  have htrace : WordTrace (prefixWord ++ tailWord_6813382) baseStart_6813382 baseEnd_6813382 := by
    simpa [prefixWord, tailWord_6813382, baseEnd_6813382] using wordTrace_append hprefix tailTrace_6813382
  have hstable : (prefixWord ++ tailWord_6813382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813382).length < 2 ^ (prefixWord ++ tailWord_6813382).sum := by decide
  have hdescent : baseEnd_6813382 < baseStart_6813382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813471 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 4, 5]
def baseStart_6813471 : Nat := 118140960795 + 6813471 * 2 ^ 59
def prefixEnd_6813471 : Nat := 4983230072969 + 3 ^ 40 * 6813471 * 2
def baseEnd_6813471 : Nat := 1166195182823405665692641

theorem tailTrace_6813471 : CollatzResearch.WordTrace tailWord_6813471 prefixEnd_6813471 1166195182823405665692641 := by
  unfold tailWord_6813471
  simp only [CollatzResearch.WordTrace]
  refine ⟨248507703098965690049144267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165671802065977126699429511 248507703098965690049144267)
  ·
    refine ⟨372761554648448535073716401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248507703098965690049144267 372761554648448535073716401)
    ·
      refine ⟨279571165986336401305287301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372761554648448535073716401 279571165986336401305287301)
      ·
        refine ⟨52419593622438075244741369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279571165986336401305287301 52419593622438075244741369)
        ·
          refine ⟨39314695216828556433556027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52419593622438075244741369 39314695216828556433556027)
          ·
            refine ⟨58972042825242834650334041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39314695216828556433556027 58972042825242834650334041)
            ·
              refine ⟨44229032118932125987750531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58972042825242834650334041 44229032118932125987750531)
              ·
                refine ⟨66343548178398188981625797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44229032118932125987750531 66343548178398188981625797)
                ·
                  refine ⟨12439415283449660434054837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66343548178398188981625797 12439415283449660434054837)
                  ·
                    refine ⟨1166195182823405665692641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12439415283449660434054837 1166195182823405665692641)
                    ·
                      rfl

theorem cell23_6813471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_6813471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813471 prefixEnd_6813471 := by exact prefixLift 6813471
  have htrace : WordTrace (prefixWord ++ tailWord_6813471) baseStart_6813471 baseEnd_6813471 := by
    simpa [prefixWord, tailWord_6813471, baseEnd_6813471] using wordTrace_append hprefix tailTrace_6813471
  have hstable : (prefixWord ++ tailWord_6813471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813471).length < 2 ^ (prefixWord ++ tailWord_6813471).sum := by decide
  have hdescent : baseEnd_6813471 < baseStart_6813471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813486 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6813486 : Nat := 118140960795 + 6813486 * 2 ^ 59
def prefixEnd_6813486 : Nat := 4983230072969 + 3 ^ 40 * 6813486 * 2
def baseEnd_6813486 : Nat := 3498593250680034438390355

theorem tailTrace_6813486 : CollatzResearch.WordTrace tailWord_6813486 prefixEnd_6813486 3498593250680034438390355 := by
  unfold tailWord_6813486
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063531274238918451367539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165672166795940898407293541 31063531274238918451367539)
  ·
    refine ⟨46595296911358377677051309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31063531274238918451367539 46595296911358377677051309)
    ·
      refine ⟨17473236341759391628894241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46595296911358377677051309 17473236341759391628894241)
      ·
        refine ⟨13104927256319543721670681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17473236341759391628894241 13104927256319543721670681)
        ·
          refine ⟨9828695442239657791253011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13104927256319543721670681 9828695442239657791253011)
          ·
            refine ⟨14743043163359486686879517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9828695442239657791253011 14743043163359486686879517)
            ·
              refine ⟨5528641186259807507579819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14743043163359486686879517 5528641186259807507579819)
              ·
                refine ⟨8292961779389711261369729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528641186259807507579819 8292961779389711261369729)
                ·
                  refine ⟨6219721334542283446027297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8292961779389711261369729 6219721334542283446027297)
                  ·
                    refine ⟨4664791000906712584520473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6219721334542283446027297 4664791000906712584520473)
                    ·
                      refine ⟨3498593250680034438390355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664791000906712584520473 3498593250680034438390355)
                      ·
                        rfl

theorem cell23_6813486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6813486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813486 prefixEnd_6813486 := by exact prefixLift 6813486
  have htrace : WordTrace (prefixWord ++ tailWord_6813486) baseStart_6813486 baseEnd_6813486 := by
    simpa [prefixWord, tailWord_6813486, baseEnd_6813486] using wordTrace_append hprefix tailTrace_6813486
  have hstable : (prefixWord ++ tailWord_6813486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813486).length < 2 ^ (prefixWord ++ tailWord_6813486).sum := by decide
  have hdescent : baseEnd_6813486 < baseStart_6813486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813535 : List Nat := [1, 1, 2, 3, 1, 6, 1, 1, 3, 4]
def baseStart_6813535 : Nat := 118140960795 + 6813535 * 2 ^ 59
def prefixEnd_6813535 : Nat := 4983230072969 + 3 ^ 40 * 6813535 * 2
def baseEnd_6813535 : Nat := 1166206137077368248892543

theorem tailTrace_6813535 : CollatzResearch.WordTrace tailWord_6813535 prefixEnd_6813535 1166206137077368248892543 := by
  unfold tailWord_6813535
  simp only [CollatzResearch.WordTrace]
  refine ⟨248510037370733828979474059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165673358247155885986316039 248510037370733828979474059)
  ·
    refine ⟨372765056056100743469211089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248510037370733828979474059 372765056056100743469211089)
    ·
      refine ⟨279573792042075557601908317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372765056056100743469211089 279573792042075557601908317)
      ·
        refine ⟨104840172015778334100715619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279573792042075557601908317 104840172015778334100715619)
        ·
          refine ⟨157260258023667501151073429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104840172015778334100715619 157260258023667501151073429)
          ·
            refine ⟨7371574594859414116456567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157260258023667501151073429 7371574594859414116456567)
            ·
              refine ⟨11057361892289121174684851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371574594859414116456567 11057361892289121174684851)
              ·
                refine ⟨16586042838433681762027277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057361892289121174684851 16586042838433681762027277)
                ·
                  refine ⟨6219766064412630660760229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16586042838433681762027277 6219766064412630660760229)
                  ·
                    refine ⟨1166206137077368248892543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219766064412630660760229 1166206137077368248892543)
                    ·
                      rfl

theorem cell23_6813535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 4].length) (baseStart_6813535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813535 prefixEnd_6813535 := by exact prefixLift 6813535
  have htrace : WordTrace (prefixWord ++ tailWord_6813535) baseStart_6813535 baseEnd_6813535 := by
    simpa [prefixWord, tailWord_6813535, baseEnd_6813535] using wordTrace_append hprefix tailTrace_6813535
  have hstable : (prefixWord ++ tailWord_6813535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813535).length < 2 ^ (prefixWord ++ tailWord_6813535).sum := by decide
  have hdescent : baseEnd_6813535 < baseStart_6813535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813548 : List Nat := [2, 2, 1, 1, 4, 3, 1, 3, 6]
def baseStart_6813548 : Nat := 118140960795 + 6813548 * 2 ^ 59
def prefixEnd_6813548 : Nat := 4983230072969 + 3 ^ 40 * 6813548 * 2
def baseEnd_6813548 : Nat := 388736120720068132868341

theorem tailTrace_6813548 : CollatzResearch.WordTrace tailWord_6813548 prefixEnd_6813548 388736120720068132868341 := by
  unfold tailWord_6813548
  simp only [CollatzResearch.WordTrace]
  refine ⟨124255255759843366099848649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165673674346457821466464865 124255255759843366099848649)
  ·
    refine ⟨93191441819882524574886487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124255255759843366099848649 93191441819882524574886487)
    ·
      refine ⟨139787162729823786862329731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93191441819882524574886487 139787162729823786862329731)
      ·
        refine ⟨209680744094735680293494597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139787162729823786862329731 209680744094735680293494597)
        ·
          refine ⟨39315139517762940055030237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209680744094735680293494597 39315139517762940055030237)
          ·
            refine ⟨14743177319161102520636339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39315139517762940055030237 14743177319161102520636339)
            ·
              refine ⟨22114765978741653780954509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14743177319161102520636339 22114765978741653780954509)
              ·
                refine ⟨8293037242028120167857941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22114765978741653780954509 8293037242028120167857941)
                ·
                  refine ⟨388736120720068132868341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8293037242028120167857941 388736120720068132868341)
                  ·
                    rfl

theorem cell23_6813548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 6].length) (baseStart_6813548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813548 prefixEnd_6813548 := by exact prefixLift 6813548
  have htrace : WordTrace (prefixWord ++ tailWord_6813548) baseStart_6813548 baseEnd_6813548 := by
    simpa [prefixWord, tailWord_6813548, baseEnd_6813548] using wordTrace_append hprefix tailTrace_6813548
  have hstable : (prefixWord ++ tailWord_6813548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813548).length < 2 ^ (prefixWord ++ tailWord_6813548).sum := by decide
  have hdescent : baseEnd_6813548 < baseStart_6813548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813582 : List Nat := [4, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_6813582 : Nat := 118140960795 + 6813582 * 2 ^ 59
def prefixEnd_6813582 : Nat := 4983230072969 + 3 ^ 40 * 6813582 * 2
def baseEnd_6813582 : Nat := 388738060535874006976657

theorem tailTrace_6813582 : CollatzResearch.WordTrace tailWord_6813582 prefixEnd_6813582 388738060535874006976657 := by
  unfold tailWord_6813582
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063968950195444500804375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165674501067709037337623333 31063968950195444500804375)
  ·
    refine ⟨46595953425293166751206563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31063968950195444500804375 46595953425293166751206563)
    ·
      refine ⟨69893930137939750126809845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46595953425293166751206563 69893930137939750126809845)
      ·
        refine ⟨6552555950431851574388423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69893930137939750126809845 6552555950431851574388423)
        ·
          refine ⟨9828833925647777361582635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552555950431851574388423 9828833925647777361582635)
          ·
            refine ⟨14743250888471666042373953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9828833925647777361582635 14743250888471666042373953)
            ·
              refine ⟨11057438166353749531780465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14743250888471666042373953 11057438166353749531780465)
              ·
                refine ⟨8293078624765312148835349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11057438166353749531780465 8293078624765312148835349)
                ·
                  refine ⟨388738060535874006976657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8293078624765312148835349 388738060535874006976657)
                  ·
                    rfl

theorem cell23_6813582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_6813582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813582 prefixEnd_6813582 := by exact prefixLift 6813582
  have htrace : WordTrace (prefixWord ++ tailWord_6813582) baseStart_6813582 baseEnd_6813582 := by
    simpa [prefixWord, tailWord_6813582, baseEnd_6813582] using wordTrace_append hprefix tailTrace_6813582
  have hstable : (prefixWord ++ tailWord_6813582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813582).length < 2 ^ (prefixWord ++ tailWord_6813582).sum := by decide
  have hdescent : baseEnd_6813582 < baseStart_6813582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813585 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 2, 3, 2]
def baseStart_6813585 : Nat := 118140960795 + 6813585 * 2 ^ 59
def prefixEnd_6813585 : Nat := 4983230072969 + 3 ^ 40 * 6813585 * 2
def baseEnd_6813585 : Nat := 3498644085264829551052399

theorem tailTrace_6813585 : CollatzResearch.WordTrace tailWord_6813585 prefixEnd_6813585 3498644085264829551052399 := by
  unfold tailWord_6813585
  simp only [CollatzResearch.WordTrace]
  refine ⟨248511861020552687518794209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165674574013701791679196139 248511861020552687518794209)
  ·
    refine ⟨186383895765414515639095657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248511861020552687518794209 186383895765414515639095657)
    ·
      refine ⟨139787921824060886729321743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186383895765414515639095657 139787921824060886729321743)
      ·
        refine ⟨209681882736091330093982615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139787921824060886729321743 209681882736091330093982615)
        ·
          refine ⟨314522824104136995140973923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209681882736091330093982615 314522824104136995140973923)
          ·
            refine ⟨471784236156205492711460885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314522824104136995140973923 471784236156205492711460885)
            ·
              refine ⟨22114886069822132470849729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 471784236156205492711460885 22114886069822132470849729)
              ·
                refine ⟨16586164552366599353137297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22114886069822132470849729 16586164552366599353137297)
                ·
                  refine ⟨12439623414274949514852973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16586164552366599353137297 12439623414274949514852973)
                  ·
                    refine ⟨4664858780353106068069865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12439623414274949514852973 4664858780353106068069865)
                    ·
                      refine ⟨3498644085264829551052399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664858780353106068069865 3498644085264829551052399)
                      ·
                        rfl

theorem cell23_6813585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_6813585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813585 prefixEnd_6813585 := by exact prefixLift 6813585
  have htrace : WordTrace (prefixWord ++ tailWord_6813585) baseStart_6813585 baseEnd_6813585 := by
    simpa [prefixWord, tailWord_6813585, baseEnd_6813585] using wordTrace_append hprefix tailTrace_6813585
  have hstable : (prefixWord ++ tailWord_6813585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813585).length < 2 ^ (prefixWord ++ tailWord_6813585).sum := by decide
  have hdescent : baseEnd_6813585 < baseStart_6813585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813586 : List Nat := [3, 2, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_6813586 : Nat := 118140960795 + 6813586 * 2 ^ 59
def prefixEnd_6813586 : Nat := 4983230072969 + 3 ^ 40 * 6813586 * 2
def baseEnd_6813586 : Nat := 1166214866248494682379965

theorem tailTrace_6813586 : CollatzResearch.WordTrace tailWord_6813586 prefixEnd_6813586 1166214866248494682379965 := by
  unfold tailWord_6813586
  simp only [CollatzResearch.WordTrace]
  refine ⟨62127974373387266172395153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165674598329032709793053741 62127974373387266172395153)
  ·
    refine ⟨46595980780040449629296365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62127974373387266172395153 46595980780040449629296365)
    ·
      refine ⟨17473492792515168610986137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46595980780040449629296365 17473492792515168610986137)
      ·
        refine ⟨13105119594386376458239603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17473492792515168610986137 13105119594386376458239603)
        ·
          refine ⟨19657679391579564687359405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13105119594386376458239603 19657679391579564687359405)
          ·
            refine ⟨7371629771842336757759777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19657679391579564687359405 7371629771842336757759777)
            ·
              refine ⟨5528722328881752568319833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7371629771842336757759777 5528722328881752568319833)
              ·
                refine ⟨4146541746661314426239875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528722328881752568319833 4146541746661314426239875)
                ·
                  refine ⟨6219812619991971639359813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146541746661314426239875 6219812619991971639359813)
                  ·
                    refine ⟨1166214866248494682379965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6219812619991971639359813 1166214866248494682379965)
                    ·
                      rfl

theorem cell23_6813586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_6813586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813586 prefixEnd_6813586 := by exact prefixLift 6813586
  have htrace : WordTrace (prefixWord ++ tailWord_6813586) baseStart_6813586 baseEnd_6813586 := by
    simpa [prefixWord, tailWord_6813586, baseEnd_6813586] using wordTrace_append hprefix tailTrace_6813586
  have hstable : (prefixWord ++ tailWord_6813586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813586).length < 2 ^ (prefixWord ++ tailWord_6813586).sum := by decide
  have hdescent : baseEnd_6813586 < baseStart_6813586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813648 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3]
def baseStart_6813648 : Nat := 118140960795 + 6813648 * 2 ^ 59
def prefixEnd_6813648 : Nat := 4983230072969 + 3 ^ 40 * 6813648 * 2
def baseEnd_6813648 : Nat := 3498676434546062804564609

theorem tailTrace_6813648 : CollatzResearch.WordTrace tailWord_6813648 prefixEnd_6813648 3498676434546062804564609 := by
  unfold tailWord_6813648
  simp only [CollatzResearch.WordTrace]
  refine ⟨124257079409662224639168799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165676105879549632852225065 124257079409662224639168799)
  ·
    refine ⟨186385619114493336958753199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124257079409662224639168799 186385619114493336958753199)
    ·
      refine ⟨279578428671740005438129799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186385619114493336958753199 279578428671740005438129799)
      ·
        refine ⟨419367643007610008157194699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279578428671740005438129799 419367643007610008157194699)
        ·
          refine ⟨629051464511415012235792049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419367643007610008157194699 629051464511415012235792049)
          ·
            refine ⟨471788598383561259176844037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629051464511415012235792049 471788598383561259176844037)
            ·
              refine ⟨88460362196917736095658257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 471788598383561259176844037 88460362196917736095658257)
              ·
                refine ⟨66345271647688302071743693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88460362196917736095658257 66345271647688302071743693)
                ·
                  refine ⟨24879476867883113276903885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66345271647688302071743693 24879476867883113276903885)
                  ·
                    refine ⟨9329803825456167478838957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24879476867883113276903885 9329803825456167478838957)
                    ·
                      refine ⟨3498676434546062804564609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9329803825456167478838957 3498676434546062804564609)
                      ·
                        rfl

theorem cell23_6813648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3].length) (baseStart_6813648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813648 prefixEnd_6813648 := by exact prefixLift 6813648
  have htrace : WordTrace (prefixWord ++ tailWord_6813648) baseStart_6813648 baseEnd_6813648 := by
    simpa [prefixWord, tailWord_6813648, baseEnd_6813648] using wordTrace_append hprefix tailTrace_6813648
  have hstable : (prefixWord ++ tailWord_6813648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813648).length < 2 ^ (prefixWord ++ tailWord_6813648).sum := by decide
  have hdescent : baseEnd_6813648 < baseStart_6813648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813665 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_6813665 : Nat := 118140960795 + 6813665 * 2 ^ 59
def prefixEnd_6813665 : Nat := 4983230072969 + 3 ^ 40 * 6813665 * 2
def baseEnd_6813665 : Nat := 3498685163717189238052031

theorem tailTrace_6813665 : CollatzResearch.WordTrace tailWord_6813665 prefixEnd_6813665 3498685163717189238052031 := by
  unfold tailWord_6813665
  simp only [CollatzResearch.WordTrace]
  refine ⟨248514778860262861181706449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165676519240175240787804299 248514778860262861181706449)
  ·
    refine ⟨186386084145197145886279837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248514778860262861181706449 186386084145197145886279837)
    ·
      refine ⟨69894781554448929707354939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186386084145197145886279837 69894781554448929707354939)
      ·
        refine ⟨104842172331673394561032409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69894781554448929707354939 104842172331673394561032409)
        ·
          refine ⟨78631629248755045920774307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104842172331673394561032409 78631629248755045920774307)
          ·
            refine ⟨117947443873132568881161461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78631629248755045920774307 117947443873132568881161461)
            ·
              refine ⟨11057572863106178332608887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117947443873132568881161461 11057572863106178332608887)
              ·
                refine ⟨16586359294659267498913331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057572863106178332608887 16586359294659267498913331)
                ·
                  refine ⟨24879538941988901248369997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16586359294659267498913331 24879538941988901248369997)
                  ·
                    refine ⟨9329827103245837968138749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24879538941988901248369997 9329827103245837968138749)
                    ·
                      refine ⟨3498685163717189238052031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9329827103245837968138749 3498685163717189238052031)
                      ·
                        rfl

theorem cell23_6813665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_6813665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813665 prefixEnd_6813665 := by exact prefixLift 6813665
  have htrace : WordTrace (prefixWord ++ tailWord_6813665) baseStart_6813665 baseEnd_6813665 := by
    simpa [prefixWord, tailWord_6813665, baseEnd_6813665] using wordTrace_append hprefix tailTrace_6813665
  have hstable : (prefixWord ++ tailWord_6813665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813665).length < 2 ^ (prefixWord ++ tailWord_6813665).sum := by decide
  have hdescent : baseEnd_6813665 < baseStart_6813665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813675 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 3, 3, 2]
def baseStart_6813675 : Nat := 118140960795 + 6813675 * 2 ^ 59
def prefixEnd_6813675 : Nat := 4983230072969 + 3 ^ 40 * 6813675 * 2
def baseEnd_6813675 : Nat := 3498690298523734198926985

theorem tailTrace_6813675 : CollatzResearch.WordTrace tailWord_6813675 prefixEnd_6813675 3498690298523734198926985 := by
  unfold tailWord_6813675
  simp only [CollatzResearch.WordTrace]
  refine ⟨248515143590226632889570479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165676762393484421926380319 248515143590226632889570479)
  ·
    refine ⟨372772715385339949334355719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248515143590226632889570479 372772715385339949334355719)
    ·
      refine ⟨559159073078009924001533579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372772715385339949334355719 559159073078009924001533579)
      ·
        refine ⟨838738609617014886002300369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559159073078009924001533579 838738609617014886002300369)
        ·
          refine ⟨629053957212761164501725277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 838738609617014886002300369 629053957212761164501725277)
          ·
            refine ⟨235895233954785436688146979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 629053957212761164501725277 235895233954785436688146979)
            ·
              refine ⟨353842850932178155032220469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235895233954785436688146979 353842850932178155032220469)
              ·
                refine ⟨33172767274891702034270669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 353842850932178155032220469 33172767274891702034270669)
                ·
                  refine ⟨12439787728084388262851501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33172767274891702034270669 12439787728084388262851501)
                  ·
                    refine ⟨4664920398031645598569313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12439787728084388262851501 4664920398031645598569313)
                    ·
                      refine ⟨3498690298523734198926985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664920398031645598569313 3498690298523734198926985)
                      ·
                        rfl

theorem cell23_6813675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3, 2].length) (baseStart_6813675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813675 prefixEnd_6813675 := by exact prefixLift 6813675
  have htrace : WordTrace (prefixWord ++ tailWord_6813675) baseStart_6813675 baseEnd_6813675 := by
    simpa [prefixWord, tailWord_6813675, baseEnd_6813675] using wordTrace_append hprefix tailTrace_6813675
  have hstable : (prefixWord ++ tailWord_6813675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813675).length < 2 ^ (prefixWord ++ tailWord_6813675).sum := by decide
  have hdescent : baseEnd_6813675 < baseStart_6813675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813692 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_6813692 : Nat := 118140960795 + 6813692 * 2 ^ 59
def prefixEnd_6813692 : Nat := 4983230072969 + 3 ^ 40 * 6813692 * 2
def baseEnd_6813692 : Nat := 3498699027694860632414407

theorem tailTrace_6813692 : CollatzResearch.WordTrace tailWord_6813692 prefixEnd_6813692 3498699027694860632414407 := by
  unfold tailWord_6813692
  simp only [CollatzResearch.WordTrace]
  refine ⟨124257881815582522396469665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165677175754110029861959553 124257881815582522396469665)
  ·
    refine ⟨93193411361686891797352249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124257881815582522396469665 93193411361686891797352249)
    ·
      refine ⟨69895058521265168848014187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93193411361686891797352249 69895058521265168848014187)
      ·
        refine ⟨104842587781897753272021281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69895058521265168848014187 104842587781897753272021281)
        ·
          refine ⟨78631940836423314954015961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104842587781897753272021281 78631940836423314954015961)
          ·
            refine ⟨58973955627317486215511971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78631940836423314954015961 58973955627317486215511971)
            ·
              refine ⟨88460933440976229323267957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58973955627317486215511971 88460933440976229323267957)
              ·
                refine ⟨8293212510091521499056371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88460933440976229323267957 8293212510091521499056371)
                ·
                  refine ⟨12439818765137282248584557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8293212510091521499056371 12439818765137282248584557)
                  ·
                    refine ⟨4664932036926480843219209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12439818765137282248584557 4664932036926480843219209)
                    ·
                      refine ⟨3498699027694860632414407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664932036926480843219209 3498699027694860632414407)
                      ·
                        rfl

theorem cell23_6813692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_6813692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813692 prefixEnd_6813692 := by exact prefixLift 6813692
  have htrace : WordTrace (prefixWord ++ tailWord_6813692) baseStart_6813692 baseEnd_6813692 := by
    simpa [prefixWord, tailWord_6813692, baseEnd_6813692] using wordTrace_append hprefix tailTrace_6813692
  have hstable : (prefixWord ++ tailWord_6813692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813692).length < 2 ^ (prefixWord ++ tailWord_6813692).sum := by decide
  have hdescent : baseEnd_6813692 < baseStart_6813692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813700 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6813700 : Nat := 118140960795 + 6813700 * 2 ^ 59
def prefixEnd_6813700 : Nat := 4983230072969 + 3 ^ 40 * 6813700 * 2
def baseEnd_6813700 : Nat := 3498703135540096601114371

theorem tailTrace_6813700 : CollatzResearch.WordTrace tailWord_6813700 prefixEnd_6813700 3498703135540096601114371 := by
  unfold tailWord_6813700
  simp only [CollatzResearch.WordTrace]
  refine ⟨124258027707568031079615277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165677370276757374772820369 124258027707568031079615277)
  ·
    refine ⟨46596760390338011654855729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124258027707568031079615277 46596760390338011654855729)
    ·
      refine ⟨34947570292753508741141797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46596760390338011654855729 34947570292753508741141797)
      ·
        refine ⟨6552669429891282888964087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34947570292753508741141797 6552669429891282888964087)
        ·
          refine ⟨9829004144836924333446131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6552669429891282888964087 9829004144836924333446131)
          ·
            refine ⟨14743506217255386500169197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9829004144836924333446131 14743506217255386500169197)
            ·
              refine ⟨5528814831470769937563449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14743506217255386500169197 5528814831470769937563449)
              ·
                refine ⟨4146611123603077453172587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528814831470769937563449 4146611123603077453172587)
                ·
                  refine ⟨6219916685404616179758881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146611123603077453172587 6219916685404616179758881)
                  ·
                    refine ⟨4664937514053462134819161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6219916685404616179758881 4664937514053462134819161)
                    ·
                      refine ⟨3498703135540096601114371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4664937514053462134819161 3498703135540096601114371)
                      ·
                        rfl

theorem cell23_6813700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6813700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813700 prefixEnd_6813700 := by exact prefixLift 6813700
  have htrace : WordTrace (prefixWord ++ tailWord_6813700) baseStart_6813700 baseEnd_6813700 := by
    simpa [prefixWord, tailWord_6813700, baseEnd_6813700] using wordTrace_append hprefix tailTrace_6813700
  have hstable : (prefixWord ++ tailWord_6813700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813700).length < 2 ^ (prefixWord ++ tailWord_6813700).sum := by decide
  have hdescent : baseEnd_6813700 < baseStart_6813700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813708 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 1, 3, 5]
def baseStart_6813708 : Nat := 118140960795 + 6813708 * 2 ^ 59
def prefixEnd_6813708 : Nat := 4983230072969 + 3 ^ 40 * 6813708 * 2
def baseEnd_6813708 : Nat := 3498707243385332569814333

theorem tailTrace_6813708 : CollatzResearch.WordTrace tailWord_6813708 prefixEnd_6813708 3498707243385332569814333 := by
  unfold tailWord_6813708
  simp only [CollatzResearch.WordTrace]
  refine ⟨124258173599553539762760889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165677564799404719683681185 124258173599553539762760889)
  ·
    refine ⟨93193630199665154822070667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124258173599553539762760889 93193630199665154822070667)
    ·
      refine ⟨139790445299497732233106001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93193630199665154822070667 139790445299497732233106001)
      ·
        refine ⟨104842833974623299174829501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139790445299497732233106001 104842833974623299174829501)
        ·
          refine ⟨39316062740483737190561063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104842833974623299174829501 39316062740483737190561063)
          ·
            refine ⟨58974094110725605785841595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39316062740483737190561063 58974094110725605785841595)
            ·
              refine ⟨88461141166088408678762393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58974094110725605785841595 88461141166088408678762393)
              ·
                refine ⟨66345855874566306509071795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88461141166088408678762393 66345855874566306509071795)
                ·
                  refine ⟨99518783811849459763607693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66345855874566306509071795 99518783811849459763607693)
                  ·
                    refine ⟨37319543929443547411352885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99518783811849459763607693 37319543929443547411352885)
                    ·
                      refine ⟨3498707243385332569814333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37319543929443547411352885 3498707243385332569814333)
                      ·
                        rfl

theorem cell23_6813708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_6813708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813708 prefixEnd_6813708 := by exact prefixLift 6813708
  have htrace : WordTrace (prefixWord ++ tailWord_6813708) baseStart_6813708 baseEnd_6813708 := by
    simpa [prefixWord, tailWord_6813708, baseEnd_6813708] using wordTrace_append hprefix tailTrace_6813708
  have hstable : (prefixWord ++ tailWord_6813708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813708).length < 2 ^ (prefixWord ++ tailWord_6813708).sum := by decide
  have hdescent : baseEnd_6813708 < baseStart_6813708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813725 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6813725 : Nat := 118140960795 + 6813725 * 2 ^ 59
def prefixEnd_6813725 : Nat := 4983230072969 + 3 ^ 40 * 6813725 * 2
def baseEnd_6813725 : Nat := 3498715972556459003301755

theorem tailTrace_6813725 : CollatzResearch.WordTrace tailWord_6813725 prefixEnd_6813725 3498715972556459003301755 := by
  unfold tailWord_6813725
  simp only [CollatzResearch.WordTrace]
  refine ⟨248516967240045491428890629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165677978160030327619260419 248516967240045491428890629)
  ·
    refine ⟨46596931357508529642916993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248516967240045491428890629 46596931357508529642916993)
    ·
      refine ⟨34947698518131397232187745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46596931357508529642916993 34947698518131397232187745)
      ·
        refine ⟨26210773888598547924140809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34947698518131397232187745 26210773888598547924140809)
        ·
          refine ⟨19658080416448910943105607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26210773888598547924140809 19658080416448910943105607)
          ·
            refine ⟨29487120624673366414658411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19658080416448910943105607 29487120624673366414658411)
            ·
              refine ⟨44230680937010049621987617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29487120624673366414658411 44230680937010049621987617)
              ·
                refine ⟨33173010702757537216490713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44230680937010049621987617 33173010702757537216490713)
                ·
                  refine ⟨24879758027068152912368035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33173010702757537216490713 24879758027068152912368035)
                  ·
                    refine ⟨37319637040602229368552053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24879758027068152912368035 37319637040602229368552053)
                    ·
                      refine ⟨3498715972556459003301755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37319637040602229368552053 3498715972556459003301755)
                      ·
                        rfl

theorem cell23_6813725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6813725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813725 prefixEnd_6813725 := by exact prefixLift 6813725
  have htrace : WordTrace (prefixWord ++ tailWord_6813725) baseStart_6813725 baseEnd_6813725 := by
    simpa [prefixWord, tailWord_6813725, baseEnd_6813725] using wordTrace_append hprefix tailTrace_6813725
  have hstable : (prefixWord ++ tailWord_6813725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813725).length < 2 ^ (prefixWord ++ tailWord_6813725).sum := by decide
  have hdescent : baseEnd_6813725 < baseStart_6813725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813768 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_6813768 : Nat := 118140960795 + 6813768 * 2 ^ 59
def prefixEnd_6813768 : Nat := 4983230072969 + 3 ^ 40 * 6813768 * 2
def baseEnd_6813768 : Nat := 3498738052224602335064057

theorem tailTrace_6813768 : CollatzResearch.WordTrace tailWord_6813768 prefixEnd_6813768 3498738052224602335064057 := by
  unfold tailWord_6813768
  simp only [CollatzResearch.WordTrace]
  refine ⟨124259267789444854886352979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165679023719259806515137305 124259267789444854886352979)
  ·
    refine ⟨186388901684167282329529469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124259267789444854886352979 186388901684167282329529469)
    ·
      refine ⟨69895838131562730873573551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186388901684167282329529469 69895838131562730873573551)
      ·
        refine ⟨104843757197344096310360327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69895838131562730873573551 104843757197344096310360327)
        ·
          refine ⟨157265635796016144465540491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104843757197344096310360327 157265635796016144465540491)
          ·
            refine ⟨235898453694024216698310737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157265635796016144465540491 235898453694024216698310737)
            ·
              refine ⟨176923840270518162523733053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235898453694024216698310737 176923840270518162523733053)
              ·
                refine ⟨66346440101444310946399895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176923840270518162523733053 66346440101444310946399895)
                ·
                  refine ⟨99519660152166466419599843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66346440101444310946399895 99519660152166466419599843)
                  ·
                    refine ⟨149279490228249699629399765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99519660152166466419599843 149279490228249699629399765)
                    ·
                      refine ⟨3498738052224602335064057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149279490228249699629399765 3498738052224602335064057)
                      ·
                        rfl

theorem cell23_6813768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_6813768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813768 prefixEnd_6813768 := by exact prefixLift 6813768
  have htrace : WordTrace (prefixWord ++ tailWord_6813768) baseStart_6813768 baseEnd_6813768 := by
    simpa [prefixWord, tailWord_6813768, baseEnd_6813768] using wordTrace_append hprefix tailTrace_6813768
  have hstable : (prefixWord ++ tailWord_6813768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813768).length < 2 ^ (prefixWord ++ tailWord_6813768).sum := by decide
  have hdescent : baseEnd_6813768 < baseStart_6813768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813792 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 2, 5]
def baseStart_6813792 : Nat := 118140960795 + 6813792 * 2 ^ 59
def prefixEnd_6813792 : Nat := 4983230072969 + 3 ^ 40 * 6813792 * 2
def baseEnd_6813792 : Nat := 1166250125253436747054649

theorem tailTrace_6813792 : CollatzResearch.WordTrace tailWord_6813792 prefixEnd_6813792 1166250125253436747054649 := by
  unfold tailWord_6813792
  simp only [CollatzResearch.WordTrace]
  refine ⟨124259705465401380935789815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165679607287201841247719753 124259705465401380935789815)
  ·
    refine ⟨186389558198102071403684723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124259705465401380935789815 186389558198102071403684723)
    ·
      refine ⟨279584337297153107105527085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186389558198102071403684723 279584337297153107105527085)
      ·
        refine ⟨104844126486432415164572657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279584337297153107105527085 104844126486432415164572657)
        ·
          refine ⟨78633094864824311373429493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104844126486432415164572657 78633094864824311373429493)
          ·
            refine ⟨7371852643577279191259015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78633094864824311373429493 7371852643577279191259015)
            ·
              refine ⟨11057778965365918786888523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371852643577279191259015 11057778965365918786888523)
              ·
                refine ⟨16586668448048878180332785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057778965365918786888523 16586668448048878180332785)
                ·
                  refine ⟨12440001336036658635249589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16586668448048878180332785 12440001336036658635249589)
                  ·
                    refine ⟨1166250125253436747054649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12440001336036658635249589 1166250125253436747054649)
                    ·
                      rfl

theorem cell23_6813792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 2, 5].length) (baseStart_6813792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813792 prefixEnd_6813792 := by exact prefixLift 6813792
  have htrace : WordTrace (prefixWord ++ tailWord_6813792) baseStart_6813792 baseEnd_6813792 := by
    simpa [prefixWord, tailWord_6813792, baseEnd_6813792] using wordTrace_append hprefix tailTrace_6813792
  have hstable : (prefixWord ++ tailWord_6813792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813792).length < 2 ^ (prefixWord ++ tailWord_6813792).sum := by decide
  have hdescent : baseEnd_6813792 < baseStart_6813792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813832 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6813832 : Nat := 118140960795 + 6813832 * 2 ^ 59
def prefixEnd_6813832 : Nat := 4983230072969 + 3 ^ 40 * 6813832 * 2
def baseEnd_6813832 : Nat := 3498770914986490084663763

theorem tailTrace_6813832 : CollatzResearch.WordTrace tailWord_6813832 prefixEnd_6813832 3498770914986490084663763 := by
  unfold tailWord_6813832
  simp only [CollatzResearch.WordTrace]
  refine ⟨124260434925328924351517875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165680579900438565802023833 124260434925328924351517875)
  ·
    refine ⟨186390652387993386527276813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124260434925328924351517875 186390652387993386527276813)
    ·
      refine ⟨69896494645497519947728805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186390652387993386527276813 69896494645497519947728805)
      ·
        refine ⟨13105592746030784990199151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69896494645497519947728805 13105592746030784990199151)
        ·
          refine ⟨19658389119046177485298727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13105592746030784990199151 19658389119046177485298727)
          ·
            refine ⟨29487583678569266227948091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19658389119046177485298727 29487583678569266227948091)
            ·
              refine ⟨44231375517853899341922137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29487583678569266227948091 44231375517853899341922137)
              ·
                refine ⟨33173531638390424506441603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44231375517853899341922137 33173531638390424506441603)
                ·
                  refine ⟨49760297457585636759662405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33173531638390424506441603 49760297457585636759662405)
                  ·
                    refine ⟨9330055773297306892436701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49760297457585636759662405 9330055773297306892436701)
                    ·
                      refine ⟨3498770914986490084663763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330055773297306892436701 3498770914986490084663763)
                      ·
                        rfl

theorem cell23_6813832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6813832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813832 prefixEnd_6813832 := by exact prefixLift 6813832
  have htrace : WordTrace (prefixWord ++ tailWord_6813832) baseStart_6813832 baseEnd_6813832 := by
    simpa [prefixWord, tailWord_6813832, baseEnd_6813832] using wordTrace_append hprefix tailTrace_6813832
  have hstable : (prefixWord ++ tailWord_6813832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813832).length < 2 ^ (prefixWord ++ tailWord_6813832).sum := by decide
  have hdescent : baseEnd_6813832 < baseStart_6813832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813845 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_6813845 : Nat := 118140960795 + 6813845 * 2 ^ 59
def prefixEnd_6813845 : Nat := 4983230072969 + 3 ^ 40 * 6813845 * 2
def baseEnd_6813845 : Nat := 3498777590234998533801203

theorem tailTrace_6813845 : CollatzResearch.WordTrace tailWord_6813845 prefixEnd_6813845 3498777590234998533801203 := by
  unfold tailWord_6813845
  simp only [CollatzResearch.WordTrace]
  refine ⟨248521343999610751923258989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165680895999740501282172659 248521343999610751923258989)
  ·
    refine ⟨93195503999854031971222121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248521343999610751923258989 93195503999854031971222121)
    ·
      refine ⟨69896627999890523978416591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93195503999854031971222121 69896627999890523978416591)
      ·
        refine ⟨104844941999835785967624887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69896627999890523978416591 104844941999835785967624887)
        ·
          refine ⟨157267412999753678951437331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104844941999835785967624887 157267412999753678951437331)
          ·
            refine ⟨235901119499630518427155997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157267412999753678951437331 235901119499630518427155997)
            ·
              refine ⟨88462919812361444410183499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235901119499630518427155997 88462919812361444410183499)
              ·
                refine ⟨132694379718542166615275249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88462919812361444410183499 132694379718542166615275249)
                ·
                  refine ⟨99520784788906624961456437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132694379718542166615275249 99520784788906624961456437)
                  ·
                    refine ⟨9330073573959996090136541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99520784788906624961456437 9330073573959996090136541)
                    ·
                      refine ⟨3498777590234998533801203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330073573959996090136541 3498777590234998533801203)
                      ·
                        rfl

theorem cell23_6813845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_6813845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813845 prefixEnd_6813845 := by exact prefixLift 6813845
  have htrace : WordTrace (prefixWord ++ tailWord_6813845) baseStart_6813845 baseEnd_6813845 := by
    simpa [prefixWord, tailWord_6813845, baseEnd_6813845] using wordTrace_append hprefix tailTrace_6813845
  have hstable : (prefixWord ++ tailWord_6813845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813845).length < 2 ^ (prefixWord ++ tailWord_6813845).sum := by decide
  have hdescent : baseEnd_6813845 < baseStart_6813845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813856 : List Nat := [2, 1, 1, 4, 2, 4, 1, 3, 1, 4]
def baseStart_6813856 : Nat := 118140960795 + 6813856 * 2 ^ 59
def prefixEnd_6813856 : Nat := 4983230072969 + 3 ^ 40 * 6813856 * 2
def baseEnd_6813856 : Nat := 1166261079507399330254551

theorem tailTrace_6813856 : CollatzResearch.WordTrace tailWord_6813856 prefixEnd_6813856 1166261079507399330254551 := by
  unfold tailWord_6813856
  simp only [CollatzResearch.WordTrace]
  refine ⟨124260872601285450400954711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165681163468380600534606281 124260872601285450400954711)
  ·
    refine ⟨186391308901928175601432067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124260872601285450400954711 186391308901928175601432067)
    ·
      refine ⟨279586963352892263402148101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186391308901928175601432067 279586963352892263402148101)
      ·
        refine ⟨52422555628667299387902769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279586963352892263402148101 52422555628667299387902769)
        ·
          refine ⟨39316916721500474540927077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52422555628667299387902769 39316916721500474540927077)
          ·
            refine ⟨7371921885281338976423827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39316916721500474540927077 7371921885281338976423827)
            ·
              refine ⟨11057882827922008464635741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7371921885281338976423827 11057882827922008464635741)
              ·
                refine ⟨4146706060470753174238403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11057882827922008464635741 4146706060470753174238403)
                ·
                  refine ⟨6220059090706129761357605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146706060470753174238403 6220059090706129761357605)
                  ·
                    refine ⟨1166261079507399330254551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220059090706129761357605 1166261079507399330254551)
                    ·
                      rfl

theorem cell23_6813856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 3, 1, 4].length) (baseStart_6813856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813856 prefixEnd_6813856 := by exact prefixLift 6813856
  have htrace : WordTrace (prefixWord ++ tailWord_6813856) baseStart_6813856 baseEnd_6813856 := by
    simpa [prefixWord, tailWord_6813856, baseEnd_6813856] using wordTrace_append hprefix tailTrace_6813856
  have hstable : (prefixWord ++ tailWord_6813856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813856).length < 2 ^ (prefixWord ++ tailWord_6813856).sum := by decide
  have hdescent : baseEnd_6813856 < baseStart_6813856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813866 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_6813866 : Nat := 118140960795 + 6813866 * 2 ^ 59
def prefixEnd_6813866 : Nat := 4983230072969 + 3 ^ 40 * 6813866 * 2
def baseEnd_6813866 : Nat := 3498788373328742951638607

theorem tailTrace_6813866 : CollatzResearch.WordTrace tailWord_6813866 prefixEnd_6813866 3498788373328742951638607 := by
  unfold tailWord_6813866
  simp only [CollatzResearch.WordTrace]
  refine ⟨62130527483133668127443363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165681406621689781673182301 62130527483133668127443363)
  ·
    refine ⟨93195791224700502191165045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62130527483133668127443363 93195791224700502191165045)
    ·
      refine ⟨8737105427315672080421723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93195791224700502191165045 8737105427315672080421723)
      ·
        refine ⟨13105658140973508120632585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8737105427315672080421723 13105658140973508120632585)
        ·
          refine ⟨9829243605730131090474439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13105658140973508120632585 9829243605730131090474439)
          ·
            refine ⟨14743865408595196635711659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9829243605730131090474439 14743865408595196635711659)
            ·
              refine ⟨22115798112892794953567489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14743865408595196635711659 22115798112892794953567489)
              ·
                refine ⟨16586848584669596215175617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22115798112892794953567489 16586848584669596215175617)
                ·
                  refine ⟨12440136438502197161381713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16586848584669596215175617 12440136438502197161381713)
                  ·
                    refine ⟨9330102328876647871036285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12440136438502197161381713 9330102328876647871036285)
                    ·
                      refine ⟨3498788373328742951638607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330102328876647871036285 3498788373328742951638607)
                      ·
                        rfl

theorem cell23_6813866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_6813866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813866 prefixEnd_6813866 := by exact prefixLift 6813866
  have htrace : WordTrace (prefixWord ++ tailWord_6813866) baseStart_6813866 baseEnd_6813866 := by
    simpa [prefixWord, tailWord_6813866, baseEnd_6813866] using wordTrace_append hprefix tailTrace_6813866
  have hstable : (prefixWord ++ tailWord_6813866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813866).length < 2 ^ (prefixWord ++ tailWord_6813866).sum := by decide
  have hdescent : baseEnd_6813866 < baseStart_6813866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813873 : List Nat := [1, 2, 2, 5, 2, 1, 3, 2, 1, 4]
def baseStart_6813873 : Nat := 118140960795 + 6813873 * 2 ^ 59
def prefixEnd_6813873 : Nat := 4983230072969 + 3 ^ 40 * 6813873 * 2
def baseEnd_6813873 : Nat := 1166263989231108141417025

theorem tailTrace_6813873 : CollatzResearch.WordTrace tailWord_6813873 prefixEnd_6813873 1166263989231108141417025 := by
  unfold tailWord_6813873
  simp only [CollatzResearch.WordTrace]
  refine ⟨248522365243509312705278273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165681576829006208470185515 248522365243509312705278273)
  ·
    refine ⟨186391773932631984528958705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248522365243509312705278273 186391773932631984528958705)
    ·
      refine ⟨139793830449473988396719029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186391773932631984528958705 139793830449473988396719029)
      ·
        refine ⟨13105671604638186412192409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139793830449473988396719029 13105671604638186412192409)
        ·
          refine ⟨9829253703478639809144307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13105671604638186412192409 9829253703478639809144307)
          ·
            refine ⟨14743880555217959713716461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9829253703478639809144307 14743880555217959713716461)
            ·
              refine ⟨5528955208206734892643673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14743880555217959713716461 5528955208206734892643673)
              ·
                refine ⟨4146716406155051169482755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5528955208206734892643673 4146716406155051169482755)
                ·
                  refine ⟨6220074609232576754224133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4146716406155051169482755 6220074609232576754224133)
                  ·
                    refine ⟨1166263989231108141417025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220074609232576754224133 1166263989231108141417025)
                    ·
                      rfl

theorem cell23_6813873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_6813873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813873 prefixEnd_6813873 := by exact prefixLift 6813873
  have htrace : WordTrace (prefixWord ++ tailWord_6813873) baseStart_6813873 baseEnd_6813873 := by
    simpa [prefixWord, tailWord_6813873, baseEnd_6813873] using wordTrace_append hprefix tailTrace_6813873
  have hstable : (prefixWord ++ tailWord_6813873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813873).length < 2 ^ (prefixWord ++ tailWord_6813873).sum := by decide
  have hdescent : baseEnd_6813873 < baseStart_6813873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813879 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 3]
def baseStart_6813879 : Nat := 118140960795 + 6813879 * 2 ^ 59
def prefixEnd_6813879 : Nat := 4983230072969 + 3 ^ 40 * 6813879 * 2
def baseEnd_6813879 : Nat := 3498795048577251400776047

theorem tailTrace_6813879 : CollatzResearch.WordTrace tailWord_6813879 prefixEnd_6813879 3498795048577251400776047 := by
  unfold tailWord_6813879
  simp only [CollatzResearch.WordTrace]
  refine ⟨248522584081487575729996691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165681722720991717153331127 248522584081487575729996691)
  ·
    refine ⟨372783876122231363594995037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248522584081487575729996691 372783876122231363594995037)
    ·
      refine ⟨139793953545836761348123139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372783876122231363594995037 139793953545836761348123139)
      ·
        refine ⟨209690930318755142022184709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139793953545836761348123139 209690930318755142022184709)
        ·
          refine ⟨39317049434766589129159633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209690930318755142022184709 39317049434766589129159633)
          ·
            refine ⟨29487787076074941846869725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39317049434766589129159633 29487787076074941846869725)
            ·
              refine ⟨11057920153528103192576147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29487787076074941846869725 11057920153528103192576147)
              ·
                refine ⟨16586880230292154788864221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057920153528103192576147 16586880230292154788864221)
                ·
                  refine ⟨6220080086359558045824083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16586880230292154788864221 6220080086359558045824083)
                  ·
                    refine ⟨9330120129539337068736125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220080086359558045824083 9330120129539337068736125)
                    ·
                      refine ⟨3498795048577251400776047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330120129539337068736125 3498795048577251400776047)
                      ·
                        rfl

theorem cell23_6813879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 3].length) (baseStart_6813879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813879 prefixEnd_6813879 := by exact prefixLift 6813879
  have htrace : WordTrace (prefixWord ++ tailWord_6813879) baseStart_6813879 baseEnd_6813879 := by
    simpa [prefixWord, tailWord_6813879, baseEnd_6813879] using wordTrace_append hprefix tailTrace_6813879
  have hstable : (prefixWord ++ tailWord_6813879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813879).length < 2 ^ (prefixWord ++ tailWord_6813879).sum := by decide
  have hdescent : baseEnd_6813879 < baseStart_6813879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813885 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6813885 : Nat := 118140960795 + 6813885 * 2 ^ 59
def prefixEnd_6813885 : Nat := 4983230072969 + 3 ^ 40 * 6813885 * 2
def baseEnd_6813885 : Nat := 3498798129461178377301019

theorem tailTrace_6813885 : CollatzResearch.WordTrace tailWord_6813885 prefixEnd_6813885 3498798129461178377301019 := by
  unfold tailWord_6813885
  simp only [CollatzResearch.WordTrace]
  refine ⟨248522802919465838754715109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165681868612977225836476739 248522802919465838754715109)
  ·
    refine ⟨46598025547399844766509083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248522802919465838754715109 46598025547399844766509083)
    ·
      refine ⟨69897038321099767149763625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46598025547399844766509083 69897038321099767149763625)
      ·
        refine ⟨52422778740824825362322719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69897038321099767149763625 52422778740824825362322719)
        ·
          refine ⟨78634168111237238043484079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52422778740824825362322719 78634168111237238043484079)
          ·
            refine ⟨117951252166855857065226119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78634168111237238043484079 117951252166855857065226119)
            ·
              refine ⟨176926878250283785597839179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117951252166855857065226119 176926878250283785597839179)
              ·
                refine ⟨265390317375425678396758769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176926878250283785597839179 265390317375425678396758769)
                ·
                  refine ⟨199042738031569258797569077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265390317375425678396758769 199042738031569258797569077)
                  ·
                    refine ⟨18660256690459618012272101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 199042738031569258797569077 18660256690459618012272101)
                    ·
                      refine ⟨3498798129461178377301019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18660256690459618012272101 3498798129461178377301019)
                      ·
                        rfl

theorem cell23_6813885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6813885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813885 prefixEnd_6813885 := by exact prefixLift 6813885
  have htrace : WordTrace (prefixWord ++ tailWord_6813885) baseStart_6813885 baseEnd_6813885 := by
    simpa [prefixWord, tailWord_6813885, baseEnd_6813885] using wordTrace_append hprefix tailTrace_6813885
  have hstable : (prefixWord ++ tailWord_6813885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813885).length < 2 ^ (prefixWord ++ tailWord_6813885).sum := by decide
  have hdescent : baseEnd_6813885 < baseStart_6813885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813886 : List Nat := [4, 2, 1, 1, 4, 2, 2, 1, 6]
def baseStart_6813886 : Nat := 118140960795 + 6813886 * 2 ^ 59
def prefixEnd_6813886 : Nat := 4983230072969 + 3 ^ 40 * 6813886 * 2
def baseEnd_6813886 : Nat := 388755404771314763709835

theorem tailTrace_6813886 : CollatzResearch.WordTrace tailWord_6813886 prefixEnd_6813886 388755404771314763709835 := by
  unfold tailWord_6813886
  simp only [CollatzResearch.WordTrace]
  refine ⟨31065354924057776990687689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165681892928308143950334341 31065354924057776990687689)
  ·
    refine ⟨23299016193043332743015767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31065354924057776990687689 23299016193043332743015767)
    ·
      refine ⟨34948524289564999114523651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23299016193043332743015767 34948524289564999114523651)
      ·
        refine ⟨52422786434347498671785477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34948524289564999114523651 52422786434347498671785477)
        ·
          refine ⟨9829272456440156000959777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52422786434347498671785477 9829272456440156000959777)
          ·
            refine ⟨7371954342330117000719833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829272456440156000959777 7371954342330117000719833)
            ·
              refine ⟨5528965756747587750539875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7371954342330117000719833 5528965756747587750539875)
              ·
                refine ⟨8293448635121381625809813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5528965756747587750539875 8293448635121381625809813)
                ·
                  refine ⟨388755404771314763709835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8293448635121381625809813 388755404771314763709835)
                  ·
                    rfl

theorem cell23_6813886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_6813886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813886 prefixEnd_6813886 := by exact prefixLift 6813886
  have htrace : WordTrace (prefixWord ++ tailWord_6813886) baseStart_6813886 baseEnd_6813886 := by
    simpa [prefixWord, tailWord_6813886, baseEnd_6813886] using wordTrace_append hprefix tailTrace_6813886
  have hstable : (prefixWord ++ tailWord_6813886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813886).length < 2 ^ (prefixWord ++ tailWord_6813886).sum := by decide
  have hdescent : baseEnd_6813886 < baseStart_6813886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813905 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_6813905 : Nat := 118140960795 + 6813905 * 2 ^ 59
def prefixEnd_6813905 : Nat := 4983230072969 + 3 ^ 40 * 6813905 * 2
def baseEnd_6813905 : Nat := 3498808399074268299050927

theorem tailTrace_6813905 : CollatzResearch.WordTrace tailWord_6813905 prefixEnd_6813905 3498808399074268299050927 := by
  unfold tailWord_6813905
  simp only [CollatzResearch.WordTrace]
  refine ⟨248523532379393382170443169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165682354919595588113628779 248523532379393382170443169)
  ·
    refine ⟨186392649284545036627832377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248523532379393382170443169 186392649284545036627832377)
    ·
      refine ⟨139794486963408777470874283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186392649284545036627832377 139794486963408777470874283)
      ·
        refine ⟨209691730445113166206311425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139794486963408777470874283 209691730445113166206311425)
        ·
          refine ⟨157268797833834874654733569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209691730445113166206311425 157268797833834874654733569)
          ·
            refine ⟨117951598375376155991050177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157268797833834874654733569 117951598375376155991050177)
            ·
              refine ⟨88463698781532116993287633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117951598375376155991050177 88463698781532116993287633)
              ·
                refine ⟨66347774086149087744965725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88463698781532116993287633 66347774086149087744965725)
                ·
                  refine ⟨24880415282305907904362147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66347774086149087744965725 24880415282305907904362147)
                  ·
                    refine ⟨37320622923458861856543221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24880415282305907904362147 37320622923458861856543221)
                    ·
                      refine ⟨3498808399074268299050927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37320622923458861856543221 3498808399074268299050927)
                      ·
                        rfl

theorem cell23_6813905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_6813905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813905 prefixEnd_6813905 := by exact prefixLift 6813905
  have htrace : WordTrace (prefixWord ++ tailWord_6813905) baseStart_6813905 baseEnd_6813905 := by
    simpa [prefixWord, tailWord_6813905, baseEnd_6813905] using wordTrace_append hprefix tailTrace_6813905
  have hstable : (prefixWord ++ tailWord_6813905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813905).length < 2 ^ (prefixWord ++ tailWord_6813905).sum := by decide
  have hdescent : baseEnd_6813905 < baseStart_6813905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813906 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_6813906 : Nat := 118140960795 + 6813906 * 2 ^ 59
def prefixEnd_6813906 : Nat := 4983230072969 + 3 ^ 40 * 6813906 * 2
def baseEnd_6813906 : Nat := 3498808912554922795138423

theorem tailTrace_6813906 : CollatzResearch.WordTrace tailWord_6813906 prefixEnd_6813906 3498808912554922795138423 := by
  unfold tailWord_6813906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62130892213097439835307393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165682379234926506227486381 62130892213097439835307393)
  ·
    refine ⟨46598169159823079876480545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62130892213097439835307393 46598169159823079876480545)
    ·
      refine ⟨34948626869867309907360409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46598169159823079876480545 34948626869867309907360409)
      ·
        refine ⟨26211470152400482430520307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34948626869867309907360409 26211470152400482430520307)
        ·
          refine ⟨39317205228600723645780461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26211470152400482430520307 39317205228600723645780461)
          ·
            refine ⟨14743951960725271367167673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39317205228600723645780461 14743951960725271367167673)
            ·
              refine ⟨11057963970543953525375755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14743951960725271367167673 11057963970543953525375755)
              ·
                refine ⟨16586945955815930288063633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11057963970543953525375755 16586945955815930288063633)
                ·
                  refine ⟨12440209466861947716047725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16586945955815930288063633 12440209466861947716047725)
                  ·
                    refine ⟨4665078550073230393517897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12440209466861947716047725 4665078550073230393517897)
                    ·
                      refine ⟨3498808912554922795138423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665078550073230393517897 3498808912554922795138423)
                      ·
                        rfl

theorem cell23_6813906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_6813906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813906 prefixEnd_6813906 := by exact prefixLift 6813906
  have htrace : WordTrace (prefixWord ++ tailWord_6813906) baseStart_6813906 baseEnd_6813906 := by
    simpa [prefixWord, tailWord_6813906, baseEnd_6813906] using wordTrace_append hprefix tailTrace_6813906
  have hstable : (prefixWord ++ tailWord_6813906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813906).length < 2 ^ (prefixWord ++ tailWord_6813906).sum := by decide
  have hdescent : baseEnd_6813906 < baseStart_6813906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813912 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 1, 6]
def baseStart_6813912 : Nat := 118140960795 + 6813912 * 2 ^ 59
def prefixEnd_6813912 : Nat := 4983230072969 + 3 ^ 40 * 6813912 * 2
def baseEnd_6813912 : Nat := 1166270664479616590554465

theorem tailTrace_6813912 : CollatzResearch.WordTrace tailWord_6813912 prefixEnd_6813912 1166270664479616590554465 := by
  unfold tailWord_6813912
  simp only [CollatzResearch.WordTrace]
  refine ⟨124261893845184011182973995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165682525126912014910631993 124261893845184011182973995)
  ·
    refine ⟨186392840767776016774460993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124261893845184011182973995 186392840767776016774460993)
    ·
      refine ⟨139794630575832012580845745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186392840767776016774460993 139794630575832012580845745)
      ·
        refine ⟨104845972931874009435634309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139794630575832012580845745 104845972931874009435634309)
        ·
          refine ⟨19658619924726376769181433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104845972931874009435634309 19658619924726376769181433)
          ·
            refine ⟨14743964943544782576886075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19658619924726376769181433 14743964943544782576886075)
            ·
              refine ⟨22115947415317173865329113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14743964943544782576886075 22115947415317173865329113)
              ·
                refine ⟨16586960561487880398996835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22115947415317173865329113 16586960561487880398996835)
                ·
                  refine ⟨24880440842231820598495253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16586960561487880398996835 24880440842231820598495253)
                  ·
                    refine ⟨1166270664479616590554465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24880440842231820598495253 1166270664479616590554465)
                    ·
                      rfl

theorem cell23_6813912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_6813912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813912 prefixEnd_6813912 := by exact prefixLift 6813912
  have htrace : WordTrace (prefixWord ++ tailWord_6813912) baseStart_6813912 baseEnd_6813912 := by
    simpa [prefixWord, tailWord_6813912, baseEnd_6813912] using wordTrace_append hprefix tailTrace_6813912
  have hstable : (prefixWord ++ tailWord_6813912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813912).length < 2 ^ (prefixWord ++ tailWord_6813912).sum := by decide
  have hdescent : baseEnd_6813912 < baseStart_6813912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813915 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4]
def baseStart_6813915 : Nat := 118140960795 + 6813915 * 2 ^ 59
def prefixEnd_6813915 : Nat := 4983230072969 + 3 ^ 40 * 6813915 * 2
def baseEnd_6813915 : Nat := 3498813533880813259925881

theorem tailTrace_6813915 : CollatzResearch.WordTrace tailWord_6813915 prefixEnd_6813915 3498813533880813259925881 := by
  unfold tailWord_6813915
  simp only [CollatzResearch.WordTrace]
  refine ⟨248523897109357153878307199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165682598072904769252204799 248523897109357153878307199)
  ·
    refine ⟨372785845664035730817460799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248523897109357153878307199 372785845664035730817460799)
    ·
      refine ⟨559178768496053596226191199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372785845664035730817460799 559178768496053596226191199)
      ·
        refine ⟨838768152744080394339286799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559178768496053596226191199 838768152744080394339286799)
        ·
          refine ⟨1258152229116120591508930199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838768152744080394339286799 1258152229116120591508930199)
          ·
            refine ⟨1887228343674180887263395299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258152229116120591508930199 1887228343674180887263395299)
            ·
              refine ⟨2830842515511271330895092949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887228343674180887263395299 2830842515511271330895092949)
              ·
                refine ⟨66347871457295421817853741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2830842515511271330895092949 66347871457295421817853741)
                ·
                  refine ⟨24880451796485783181695153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66347871457295421817853741 24880451796485783181695153)
                  ·
                    refine ⟨18660338847364337386271365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24880451796485783181695153 18660338847364337386271365)
                    ·
                      refine ⟨3498813533880813259925881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18660338847364337386271365 3498813533880813259925881)
                      ·
                        rfl

theorem cell23_6813915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_6813915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813915 prefixEnd_6813915 := by exact prefixLift 6813915
  have htrace : WordTrace (prefixWord ++ tailWord_6813915) baseStart_6813915 baseEnd_6813915 := by
    simpa [prefixWord, tailWord_6813915, baseEnd_6813915] using wordTrace_append hprefix tailTrace_6813915
  have hstable : (prefixWord ++ tailWord_6813915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813915).length < 2 ^ (prefixWord ++ tailWord_6813915).sum := by decide
  have hdescent : baseEnd_6813915 < baseStart_6813915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813925 : List Nat := [1, 3, 1, 4, 2, 12]
def baseStart_6813925 : Nat := 118140960795 + 6813925 * 2 ^ 59
def prefixEnd_6813925 : Nat := 4983230072969 + 3 ^ 40 * 6813925 * 2
def baseEnd_6813925 : Nat := 14398430735338922719345

theorem tailTrace_6813925 : CollatzResearch.WordTrace tailWord_6813925 prefixEnd_6813925 14398430735338922719345 := by
  unfold tailWord_6813925
  simp only [CollatzResearch.WordTrace]
  refine ⟨248524261839320925586171229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165682841226213950390780819 248524261839320925586171229)
  ·
    refine ⟨93196598189745347094814211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248524261839320925586171229 93196598189745347094814211)
    ·
      refine ⟨139794897284618020642221317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93196598189745347094814211 139794897284618020642221317)
      ·
        refine ⟨26211543240865878870416497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139794897284618020642221317 26211543240865878870416497)
        ·
          refine ⟨19658657430649409152812373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26211543240865878870416497 19658657430649409152812373)
          ·
            refine ⟨14398430735338922719345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19658657430649409152812373 14398430735338922719345)
            ·
              rfl

theorem cell23_6813925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 12].length) (baseStart_6813925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813925 prefixEnd_6813925 := by exact prefixLift 6813925
  have htrace : WordTrace (prefixWord ++ tailWord_6813925) baseStart_6813925 baseEnd_6813925 := by
    simpa [prefixWord, tailWord_6813925, baseEnd_6813925] using wordTrace_append hprefix tailTrace_6813925
  have hstable : (prefixWord ++ tailWord_6813925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813925).length < 2 ^ (prefixWord ++ tailWord_6813925).sum := by decide
  have hdescent : baseEnd_6813925 < baseStart_6813925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813942 : List Nat := [5, 1, 1, 1, 1, 1, 5, 8]
def baseStart_6813942 : Nat := 118140960795 + 6813942 * 2 ^ 59
def prefixEnd_6813942 : Nat := 4983230072969 + 3 ^ 40 * 6813942 * 2
def baseEnd_6813942 : Nat := 129586199920684616825491

theorem tailTrace_6813942 : CollatzResearch.WordTrace tailWord_6813942 prefixEnd_6813942 129586199920684616825491 := by
  unfold tailWord_6813942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532805117516208593096255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165683254586839558326360053 15532805117516208593096255)
  ·
    refine ⟨23299207676274312889644383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15532805117516208593096255 23299207676274312889644383)
    ·
      refine ⟨34948811514411469334466575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23299207676274312889644383 34948811514411469334466575)
      ·
        refine ⟨52423217271617204001699863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34948811514411469334466575 52423217271617204001699863)
        ·
          refine ⟨78634825907425806002549795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52423217271617204001699863 78634825907425806002549795)
          ·
            refine ⟨117952238861138709003824693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78634825907425806002549795 117952238861138709003824693)
            ·
              refine ⟨11058022393231753969108565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117952238861138709003824693 11058022393231753969108565)
              ·
                refine ⟨129586199920684616825491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11058022393231753969108565 129586199920684616825491)
                ·
                  rfl

theorem cell23_6813942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_6813942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813942 prefixEnd_6813942 := by exact prefixLift 6813942
  have htrace : WordTrace (prefixWord ++ tailWord_6813942) baseStart_6813942 baseEnd_6813942 := by
    simpa [prefixWord, tailWord_6813942, baseEnd_6813942] using wordTrace_append hprefix tailTrace_6813942
  have hstable : (prefixWord ++ tailWord_6813942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813942).length < 2 ^ (prefixWord ++ tailWord_6813942).sum := by decide
  have hdescent : baseEnd_6813942 < baseStart_6813942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813952 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3]
def baseStart_6813952 : Nat := 118140960795 + 6813952 * 2 ^ 59
def prefixEnd_6813952 : Nat := 4983230072969 + 3 ^ 40 * 6813952 * 2
def baseEnd_6813952 : Nat := 3498832532665029615163211

theorem tailTrace_6813952 : CollatzResearch.WordTrace tailWord_6813952 prefixEnd_6813952 3498832532665029615163211 := by
  unfold tailWord_6813952
  simp only [CollatzResearch.WordTrace]
  refine ⟨124262623305111554598702055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165683497740148739464936073 124262623305111554598702055)
  ·
    refine ⟨186393934957667331898053083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124262623305111554598702055 186393934957667331898053083)
    ·
      refine ⟨279590902436500997847079625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186393934957667331898053083 279590902436500997847079625)
      ·
        refine ⟨209693176827375748385309719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279590902436500997847079625 209693176827375748385309719)
        ·
          refine ⟨314539765241063622577964579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209693176827375748385309719 314539765241063622577964579)
          ·
            refine ⟨471809647861595433866946869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314539765241063622577964579 471809647861595433866946869)
            ·
              refine ⟨44232154487024571925026269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 471809647861595433866946869 44232154487024571925026269)
              ·
                refine ⟨16587057932634214471884851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44232154487024571925026269 16587057932634214471884851)
                ·
                  refine ⟨24880586898951321707827277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16587057932634214471884851 24880586898951321707827277)
                  ·
                    refine ⟨9330220087106745640435229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24880586898951321707827277 9330220087106745640435229)
                    ·
                      refine ⟨3498832532665029615163211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330220087106745640435229 3498832532665029615163211)
                      ·
                        rfl

theorem cell23_6813952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 3].length) (baseStart_6813952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813952 prefixEnd_6813952 := by exact prefixLift 6813952
  have htrace : WordTrace (prefixWord ++ tailWord_6813952) baseStart_6813952 baseEnd_6813952 := by
    simpa [prefixWord, tailWord_6813952, baseEnd_6813952] using wordTrace_append hprefix tailTrace_6813952
  have hstable : (prefixWord ++ tailWord_6813952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813952).length < 2 ^ (prefixWord ++ tailWord_6813952).sum := by decide
  have hdescent : baseEnd_6813952 < baseStart_6813952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813955 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 2, 7]
def baseStart_6813955 : Nat := 118140960795 + 6813955 * 2 ^ 59
def prefixEnd_6813955 : Nat := 4983230072969 + 3 ^ 40 * 6813955 * 2
def baseEnd_6813955 : Nat := 1166278024368997701141899

theorem tailTrace_6813955 : CollatzResearch.WordTrace tailWord_6813955 prefixEnd_6813955 1166278024368997701141899 := by
  unfold tailWord_6813955
  simp only [CollatzResearch.WordTrace]
  refine ⟨248525356029212240709763319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165683570686141493806508879 248525356029212240709763319)
  ·
    refine ⟨372788034043818361064644979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248525356029212240709763319 372788034043818361064644979)
    ·
      refine ⟨559182051065727541596967469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372788034043818361064644979 559182051065727541596967469)
      ·
        refine ⟨209693269149647828098862801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 559182051065727541596967469 209693269149647828098862801)
        ·
          refine ⟨157269951862235871074147101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209693269149647828098862801 157269951862235871074147101)
          ·
            refine ⟨58976231948338451652805163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157269951862235871074147101 58976231948338451652805163)
            ·
              refine ⟨88464347922507677479207745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58976231948338451652805163 88464347922507677479207745)
              ·
                refine ⟨66348260941880758109405809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88464347922507677479207745 66348260941880758109405809)
                ·
                  refine ⟨49761195706410568582054357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66348260941880758109405809 49761195706410568582054357)
                  ·
                    refine ⟨1166278024368997701141899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49761195706410568582054357 1166278024368997701141899)
                    ·
                      rfl

theorem cell23_6813955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_6813955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813955 prefixEnd_6813955 := by exact prefixLift 6813955
  have htrace : WordTrace (prefixWord ++ tailWord_6813955) baseStart_6813955 baseEnd_6813955 := by
    simpa [prefixWord, tailWord_6813955, baseEnd_6813955] using wordTrace_append hprefix tailTrace_6813955
  have hstable : (prefixWord ++ tailWord_6813955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813955).length < 2 ^ (prefixWord ++ tailWord_6813955).sum := by decide
  have hdescent : baseEnd_6813955 < baseStart_6813955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6813986 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_6813986 : Nat := 118140960795 + 6813986 * 2 ^ 59
def prefixEnd_6813986 : Nat := 4983230072969 + 3 ^ 40 * 6813986 * 2
def baseEnd_6813986 : Nat := 3498849991007282482138055

theorem tailTrace_6813986 : CollatzResearch.WordTrace tailWord_6813986 prefixEnd_6813986 3498849991007282482138055 := by
  unfold tailWord_6813986
  simp only [CollatzResearch.WordTrace]
  refine ⟨62131621673024983251035453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165684324461399955336094541 62131621673024983251035453)
  ·
    refine ⟨23299358127384368719138295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62131621673024983251035453 23299358127384368719138295)
    ·
      refine ⟨34949037191076553078707443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23299358127384368719138295 34949037191076553078707443)
      ·
        refine ⟨52423555786614829618061165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34949037191076553078707443 52423555786614829618061165)
        ·
          refine ⟨19658833419980561106772937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52423555786614829618061165 19658833419980561106772937)
          ·
            refine ⟨14744125064985420830079703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19658833419980561106772937 14744125064985420830079703)
            ·
              refine ⟨22116187597478131245119555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14744125064985420830079703 22116187597478131245119555)
              ·
                refine ⟨33174281396217196867679333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22116187597478131245119555 33174281396217196867679333)
                ·
                  refine ⟨6220177761790724412689875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33174281396217196867679333 6220177761790724412689875)
                  ·
                    refine ⟨9330266642686086619034813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220177761790724412689875 9330266642686086619034813)
                    ·
                      refine ⟨3498849991007282482138055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330266642686086619034813 3498849991007282482138055)
                      ·
                        rfl

theorem cell23_6813986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_6813986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6813986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6813986 prefixEnd_6813986 := by exact prefixLift 6813986
  have htrace : WordTrace (prefixWord ++ tailWord_6813986) baseStart_6813986 baseEnd_6813986 := by
    simpa [prefixWord, tailWord_6813986, baseEnd_6813986] using wordTrace_append hprefix tailTrace_6813986
  have hstable : (prefixWord ++ tailWord_6813986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6813986).length < 2 ^ (prefixWord ++ tailWord_6813986).sum := by decide
  have hdescent : baseEnd_6813986 < baseStart_6813986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6813986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814012 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_6814012 : Nat := 118140960795 + 6814012 * 2 ^ 59
def prefixEnd_6814012 : Nat := 4983230072969 + 3 ^ 40 * 6814012 * 2
def baseEnd_6814012 : Nat := 3498863341504299380412935

theorem tailTrace_6814012 : CollatzResearch.WordTrace tailWord_6814012 prefixEnd_6814012 3498863341504299380412935 := by
  unfold tailWord_6814012
  simp only [CollatzResearch.WordTrace]
  refine ⟨124263717495002869722294145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165684956660003826296392193 124263717495002869722294145)
  ·
    refine ⟨93197788121252152291720609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124263717495002869722294145 93197788121252152291720609)
    ·
      refine ⟨69898341090939114218790457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93197788121252152291720609 69898341090939114218790457)
      ·
        refine ⟨52423755818204335664092843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69898341090939114218790457 52423755818204335664092843)
        ·
          refine ⟨78635633727306503496139265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52423755818204335664092843 78635633727306503496139265)
          ·
            refine ⟨58976725295479877622104449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78635633727306503496139265 58976725295479877622104449)
            ·
              refine ⟨44232543971609908216578337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58976725295479877622104449 44232543971609908216578337)
              ·
                refine ⟨33174407978707431162433753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44232543971609908216578337 33174407978707431162433753)
                ·
                  refine ⟨24880805984030573371825315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33174407978707431162433753 24880805984030573371825315)
                  ·
                    refine ⟨37321208976045860057737973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24880805984030573371825315 37321208976045860057737973)
                    ·
                      refine ⟨3498863341504299380412935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37321208976045860057737973 3498863341504299380412935)
                      ·
                        rfl

theorem cell23_6814012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_6814012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814012 prefixEnd_6814012 := by exact prefixLift 6814012
  have htrace : WordTrace (prefixWord ++ tailWord_6814012) baseStart_6814012 baseEnd_6814012 := by
    simpa [prefixWord, tailWord_6814012, baseEnd_6814012] using wordTrace_append hprefix tailTrace_6814012
  have hstable : (prefixWord ++ tailWord_6814012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814012).length < 2 ^ (prefixWord ++ tailWord_6814012).sum := by decide
  have hdescent : baseEnd_6814012 < baseStart_6814012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814100 : List Nat := [2, 4, 2, 1, 3, 2, 2, 2, 5]
def baseStart_6814100 : Nat := 118140960795 + 6814100 * 2 ^ 59
def prefixEnd_6814100 : Nat := 4983230072969 + 3 ^ 40 * 6814100 * 2
def baseEnd_6814100 : Nat := 388767614200210559568059

theorem tailTrace_6814100 : CollatzResearch.WordTrace tailWord_6814100 prefixEnd_6814100 388767614200210559568059 := by
  unfold tailWord_6814100
  simp only [CollatzResearch.WordTrace]
  refine ⟨124265322306843465236895877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165687096409124620315861169 124265322306843465236895877)
  ·
    refine ⟨23299747932533149731917977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124265322306843465236895877 23299747932533149731917977)
    ·
      refine ⟨17474810949399862298938483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23299747932533149731917977 17474810949399862298938483)
      ·
        refine ⟨26212216424099793448407725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17474810949399862298938483 26212216424099793448407725)
        ·
          refine ⟨9829581159037422543152897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26212216424099793448407725 9829581159037422543152897)
          ·
            refine ⟨7372185869278066907364673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829581159037422543152897 7372185869278066907364673)
            ·
              refine ⟨5529139401958550180523505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7372185869278066907364673 5529139401958550180523505)
              ·
                refine ⟨4146854551468912635392629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529139401958550180523505 4146854551468912635392629)
                ·
                  refine ⟨388767614200210559568059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4146854551468912635392629 388767614200210559568059)
                  ·
                    rfl

theorem cell23_6814100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_6814100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814100 prefixEnd_6814100 := by exact prefixLift 6814100
  have htrace : WordTrace (prefixWord ++ tailWord_6814100) baseStart_6814100 baseEnd_6814100 := by
    simpa [prefixWord, tailWord_6814100, baseEnd_6814100] using wordTrace_append hprefix tailTrace_6814100
  have hstable : (prefixWord ++ tailWord_6814100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814100).length < 2 ^ (prefixWord ++ tailWord_6814100).sum := by decide
  have hdescent : baseEnd_6814100 < baseStart_6814100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814133 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_6814133 : Nat := 118140960795 + 6814133 * 2 ^ 59
def prefixEnd_6814133 : Nat := 4983230072969 + 3 ^ 40 * 6814133 * 2
def baseEnd_6814133 : Nat := 3498925472663493406999879

theorem tailTrace_6814133 : CollatzResearch.WordTrace tailWord_6814133 prefixEnd_6814133 3498925472663493406999879 := by
  unfold tailWord_6814133
  simp only [CollatzResearch.WordTrace]
  refine ⟨248531848222567377109743053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165687898815044918073162035 248531848222567377109743053)
  ·
    refine ⟨93199443083462766416153645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248531848222567377109743053 93199443083462766416153645)
    ·
      refine ⟨34949791156298537406057617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93199443083462766416153645 34949791156298537406057617)
      ·
        refine ⟨26212343367223903054543213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34949791156298537406057617 26212343367223903054543213)
        ·
          refine ⟨9829628762708963645453705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26212343367223903054543213 9829628762708963645453705)
          ·
            refine ⟨7372221572031722734090279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829628762708963645453705 7372221572031722734090279)
            ·
              refine ⟨11058332358047584101135419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372221572031722734090279 11058332358047584101135419)
              ·
                refine ⟨16587498537071376151703129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11058332358047584101135419 16587498537071376151703129)
                ·
                  refine ⟨12440623902803532113777347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16587498537071376151703129 12440623902803532113777347)
                  ·
                    refine ⟨18660935854205298170666021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12440623902803532113777347 18660935854205298170666021)
                    ·
                      refine ⟨3498925472663493406999879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18660935854205298170666021 3498925472663493406999879)
                      ·
                        rfl

theorem cell23_6814133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_6814133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814133 prefixEnd_6814133 := by exact prefixLift 6814133
  have htrace : WordTrace (prefixWord ++ tailWord_6814133) baseStart_6814133 baseEnd_6814133 := by
    simpa [prefixWord, tailWord_6814133, baseEnd_6814133] using wordTrace_append hprefix tailTrace_6814133
  have hstable : (prefixWord ++ tailWord_6814133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814133).length < 2 ^ (prefixWord ++ tailWord_6814133).sum := by decide
  have hdescent : baseEnd_6814133 < baseStart_6814133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814186 : List Nat := [3, 1, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_6814186 : Nat := 118140960795 + 6814186 * 2 ^ 59
def prefixEnd_6814186 : Nat := 4983230072969 + 3 ^ 40 * 6814186 * 2
def baseEnd_6814186 : Nat := 1166317562379393899879045

theorem tailTrace_6814186 : CollatzResearch.WordTrace tailWord_6814186 prefixEnd_6814186 1166317562379393899879045 := by
  unfold tailWord_6814186
  simp only [CollatzResearch.WordTrace]
  refine ⟨62133445322843841790355603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165689187527583578107614941 62133445322843841790355603)
  ·
    refine ⟨93200167984265762685533405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62133445322843841790355603 93200167984265762685533405)
    ·
      refine ⟨34950062994099661007075027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93200167984265762685533405 34950062994099661007075027)
      ·
        refine ⟨52425094491149491510612541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34950062994099661007075027 52425094491149491510612541)
        ·
          refine ⟨19659410434181059316479703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52425094491149491510612541 19659410434181059316479703)
          ·
            refine ⟨29489115651271588974719555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19659410434181059316479703 29489115651271588974719555)
            ·
              refine ⟨44233673476907383462079333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29489115651271588974719555 44233673476907383462079333)
              ·
                refine ⟨8293813776920134399139875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44233673476907383462079333 8293813776920134399139875)
                ·
                  refine ⟨12440720665380201598709813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8293813776920134399139875 12440720665380201598709813)
                  ·
                    refine ⟨1166317562379393899879045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12440720665380201598709813 1166317562379393899879045)
                    ·
                      rfl

theorem cell23_6814186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_6814186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814186 prefixEnd_6814186 := by exact prefixLift 6814186
  have htrace : WordTrace (prefixWord ++ tailWord_6814186) baseStart_6814186 baseEnd_6814186 := by
    simpa [prefixWord, tailWord_6814186, baseEnd_6814186] using wordTrace_append hprefix tailTrace_6814186
  have hstable : (prefixWord ++ tailWord_6814186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814186).length < 2 ^ (prefixWord ++ tailWord_6814186).sum := by decide
  have hdescent : baseEnd_6814186 < baseStart_6814186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814216 : List Nat := [2, 1, 3, 2, 1, 1, 1, 6, 2, 4]
def baseStart_6814216 : Nat := 118140960795 + 6814216 * 2 ^ 59
def prefixEnd_6814216 : Nat := 4983230072969 + 3 ^ 40 * 6814216 * 2
def baseEnd_6814216 : Nat := 1166322697185938860753999

theorem tailTrace_6814216 : CollatzResearch.WordTrace tailWord_6814216 prefixEnd_6814216 1166322697185938860753999 := by
  unfold tailWord_6814216
  simp only [CollatzResearch.WordTrace]
  refine ⟨124267437740633341142507251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165689916987511121523343001 124267437740633341142507251)
  ·
    refine ⟨186401156610950011713760877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124267437740633341142507251 186401156610950011713760877)
    ·
      refine ⟨69900433729106254392660329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186401156610950011713760877 69900433729106254392660329)
      ·
        refine ⟨52425325296829690794495247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69900433729106254392660329 52425325296829690794495247)
        ·
          refine ⟨78637987945244536191742871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52425325296829690794495247 78637987945244536191742871)
          ·
            refine ⟨117956981917866804287614307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78637987945244536191742871 117956981917866804287614307)
            ·
              refine ⟨176935472876800206431421461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117956981917866804287614307 176935472876800206431421461)
              ·
                refine ⟨8293850291100009676472881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 176935472876800206431421461 8293850291100009676472881)
                ·
                  refine ⟨6220387718325007257354661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8293850291100009676472881 6220387718325007257354661)
                  ·
                    refine ⟨1166322697185938860753999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220387718325007257354661 1166322697185938860753999)
                    ·
                      rfl

theorem cell23_6814216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_6814216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814216 prefixEnd_6814216 := by exact prefixLift 6814216
  have htrace : WordTrace (prefixWord ++ tailWord_6814216) baseStart_6814216 baseEnd_6814216 := by
    simpa [prefixWord, tailWord_6814216, baseEnd_6814216] using wordTrace_append hprefix tailTrace_6814216
  have hstable : (prefixWord ++ tailWord_6814216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814216).length < 2 ^ (prefixWord ++ tailWord_6814216).sum := by decide
  have hdescent : baseEnd_6814216 < baseStart_6814216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814219 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6]
def baseStart_6814219 : Nat := 118140960795 + 6814219 * 2 ^ 59
def prefixEnd_6814219 : Nat := 4983230072969 + 3 ^ 40 * 6814219 * 2
def baseEnd_6814219 : Nat := 3498969631999780070524483

theorem tailTrace_6814219 : CollatzResearch.WordTrace tailWord_6814219 prefixEnd_6814219 3498969631999780070524483 := by
  unfold tailWord_6814219
  simp only [CollatzResearch.WordTrace]
  refine ⟨248534984900255813797373711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165689989933503875864915807 248534984900255813797373711)
  ·
    refine ⟨372802477350383720696060567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248534984900255813797373711 372802477350383720696060567)
    ·
      refine ⟨559203716025575581044090851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372802477350383720696060567 559203716025575581044090851)
      ·
        refine ⟨838805574038363371566136277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559203716025575581044090851 838805574038363371566136277)
        ·
          refine ⟨19659505641524141521081319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 838805574038363371566136277 19659505641524141521081319)
          ·
            refine ⟨29489258462286212281621979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19659505641524141521081319 29489258462286212281621979)
            ·
              refine ⟨44233887693429318422432969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29489258462286212281621979 44233887693429318422432969)
              ·
                refine ⟨33175415770071988816824727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44233887693429318422432969 33175415770071988816824727)
                ·
                  refine ⟨49763123655107983225237091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33175415770071988816824727 49763123655107983225237091)
                  ·
                    refine ⟨74644685482661974837855637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49763123655107983225237091 74644685482661974837855637)
                    ·
                      refine ⟨3498969631999780070524483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74644685482661974837855637 3498969631999780070524483)
                      ·
                        rfl

theorem cell23_6814219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_6814219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814219 prefixEnd_6814219 := by exact prefixLift 6814219
  have htrace : WordTrace (prefixWord ++ tailWord_6814219) baseStart_6814219 baseEnd_6814219 := by
    simpa [prefixWord, tailWord_6814219, baseEnd_6814219] using wordTrace_append hprefix tailTrace_6814219
  have hstable : (prefixWord ++ tailWord_6814219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814219).length < 2 ^ (prefixWord ++ tailWord_6814219).sum := by decide
  have hdescent : baseEnd_6814219 < baseStart_6814219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814229 : List Nat := [1, 3, 2, 1, 3, 1, 4, 8]
def baseStart_6814229 : Nat := 118140960795 + 6814229 * 2 ^ 59
def prefixEnd_6814229 : Nat := 4983230072969 + 3 ^ 40 * 6814229 * 2
def baseEnd_6814229 : Nat := 129591658029863890051831

theorem tailTrace_6814229 : CollatzResearch.WordTrace tailWord_6814229 prefixEnd_6814229 129591658029863890051831 := by
  unfold tailWord_6814229
  simp only [CollatzResearch.WordTrace]
  refine ⟨248535349630219585505237741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165690233086813057003491827 248535349630219585505237741)
  ·
    refine ⟨93200756111332344564464153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248535349630219585505237741 93200756111332344564464153)
    ·
      refine ⟨69900567083499258423348115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93200756111332344564464153 69900567083499258423348115)
      ·
        refine ⟨104850850625248887635022173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69900567083499258423348115 104850850625248887635022173)
        ·
          refine ⟨39319068984468332863133315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104850850625248887635022173 39319068984468332863133315)
          ·
            refine ⟨58978603476702499294699973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39319068984468332863133315 58978603476702499294699973)
            ·
              refine ⟨11058488151881718617756245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58978603476702499294699973 11058488151881718617756245)
              ·
                refine ⟨129591658029863890051831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11058488151881718617756245 129591658029863890051831)
                ·
                  rfl

theorem cell23_6814229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 8].length) (baseStart_6814229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814229 prefixEnd_6814229 := by exact prefixLift 6814229
  have htrace : WordTrace (prefixWord ++ tailWord_6814229) baseStart_6814229 baseEnd_6814229 := by
    simpa [prefixWord, tailWord_6814229, baseEnd_6814229] using wordTrace_append hprefix tailTrace_6814229
  have hstable : (prefixWord ++ tailWord_6814229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814229).length < 2 ^ (prefixWord ++ tailWord_6814229).sum := by decide
  have hdescent : baseEnd_6814229 < baseStart_6814229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814240 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6814240 : Nat := 118140960795 + 6814240 * 2 ^ 59
def prefixEnd_6814240 : Nat := 4983230072969 + 3 ^ 40 * 6814240 * 2
def baseEnd_6814240 : Nat := 3498980415093524488361887

theorem tailTrace_6814240 : CollatzResearch.WordTrace tailWord_6814240 prefixEnd_6814240 3498980415093524488361887 := by
  unfold tailWord_6814240
  simp only [CollatzResearch.WordTrace]
  refine ⟨124267875416589867191944087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165690500555453156255925449 124267875416589867191944087)
  ·
    refine ⟨186401813124884800787916131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124267875416589867191944087 186401813124884800787916131)
    ·
      refine ⟨279602719687327201181874197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186401813124884800787916131 279602719687327201181874197)
      ·
        refine ⟨13106377485343462555400353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 279602719687327201181874197 13106377485343462555400353)
        ·
          refine ⟨9829783114007596916550265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13106377485343462555400353 9829783114007596916550265)
          ·
            refine ⟨7372337335505697687412699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9829783114007596916550265 7372337335505697687412699)
            ·
              refine ⟨11058506003258546531119049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372337335505697687412699 11058506003258546531119049)
              ·
                refine ⟨8293879502443909898339287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11058506003258546531119049 8293879502443909898339287)
                ·
                  refine ⟨12440819253665864847508931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8293879502443909898339287 12440819253665864847508931)
                  ·
                    refine ⟨18661228880498797271263397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12440819253665864847508931 18661228880498797271263397)
                    ·
                      refine ⟨3498980415093524488361887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18661228880498797271263397 3498980415093524488361887)
                      ·
                        rfl

theorem cell23_6814240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6814240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814240 prefixEnd_6814240 := by exact prefixLift 6814240
  have htrace : WordTrace (prefixWord ++ tailWord_6814240) baseStart_6814240 baseEnd_6814240 := by
    simpa [prefixWord, tailWord_6814240, baseEnd_6814240] using wordTrace_append hprefix tailTrace_6814240
  have hstable : (prefixWord ++ tailWord_6814240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814240).length < 2 ^ (prefixWord ++ tailWord_6814240).sum := by decide
  have hdescent : baseEnd_6814240 < baseStart_6814240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814243 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 3]
def baseStart_6814243 : Nat := 118140960795 + 6814243 * 2 ^ 59
def prefixEnd_6814243 : Nat := 4983230072969 + 3 ^ 40 * 6814243 * 2
def baseEnd_6814243 : Nat := 3498981955535487976624373

theorem tailTrace_6814243 : CollatzResearch.WordTrace tailWord_6814243 prefixEnd_6814243 3498981955535487976624373 := by
  unfold tailWord_6814243
  simp only [CollatzResearch.WordTrace]
  refine ⟨248535860252168865896247383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165690573501445910597498255 248535860252168865896247383)
  ·
    refine ⟨372803790378253298844371075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248535860252168865896247383 372803790378253298844371075)
    ·
      refine ⟨559205685567379948266556613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372803790378253298844371075 559205685567379948266556613)
      ·
        refine ⟨104851066043883740299979365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 559205685567379948266556613 104851066043883740299979365)
        ·
          refine ⟨19659574883228201306246131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104851066043883740299979365 19659574883228201306246131)
          ·
            refine ⟨29489362324842301959369197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19659574883228201306246131 29489362324842301959369197)
            ·
              refine ⟨11058510871815863234763449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29489362324842301959369197 11058510871815863234763449)
              ·
                refine ⟨8293883153861897426072587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11058510871815863234763449 8293883153861897426072587)
                ·
                  refine ⟨12440824730792846139108881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8293883153861897426072587 12440824730792846139108881)
                  ·
                    refine ⟨9330618548094634604331661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12440824730792846139108881 9330618548094634604331661)
                    ·
                      refine ⟨3498981955535487976624373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330618548094634604331661 3498981955535487976624373)
                      ·
                        rfl

theorem cell23_6814243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_6814243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814243 prefixEnd_6814243 := by exact prefixLift 6814243
  have htrace : WordTrace (prefixWord ++ tailWord_6814243) baseStart_6814243 baseEnd_6814243 := by
    simpa [prefixWord, tailWord_6814243, baseEnd_6814243] using wordTrace_append hprefix tailTrace_6814243
  have hstable : (prefixWord ++ tailWord_6814243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814243).length < 2 ^ (prefixWord ++ tailWord_6814243).sum := by decide
  have hdescent : baseEnd_6814243 < baseStart_6814243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814256 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 6, 1, 3]
def baseStart_6814256 : Nat := 118140960795 + 6814256 * 2 ^ 59
def prefixEnd_6814256 : Nat := 4983230072969 + 3 ^ 40 * 6814256 * 2
def baseEnd_6814256 : Nat := 3498988630783996425761813

theorem tailTrace_6814256 : CollatzResearch.WordTrace tailWord_6814256 prefixEnd_6814256 3498988630783996425761813 := by
  unfold tailWord_6814256
  simp only [CollatzResearch.WordTrace]
  refine ⟨124268167200560884558235311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165690889600747846077647081 124268167200560884558235311)
  ·
    refine ⟨186402250800841326837352967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124268167200560884558235311 186402250800841326837352967)
    ·
      refine ⟨279603376201261990256029451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186402250800841326837352967 279603376201261990256029451)
      ·
        refine ⟨419405064301892985384044177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279603376201261990256029451 419405064301892985384044177)
        ·
          refine ⟨314553798226419739038033133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419405064301892985384044177 314553798226419739038033133)
          ·
            refine ⟨117957674334907402139262425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314553798226419739038033133 117957674334907402139262425)
            ·
              refine ⟨88468255751180551604446819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117957674334907402139262425 88468255751180551604446819)
              ·
                refine ⟨132702383626770827406670229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88468255751180551604446819 132702383626770827406670229)
                ·
                  refine ⟨6220424232504882534687667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132702383626770827406670229 6220424232504882534687667)
                  ·
                    refine ⟨9330636348757323802031501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220424232504882534687667 9330636348757323802031501)
                    ·
                      refine ⟨3498988630783996425761813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330636348757323802031501 3498988630783996425761813)
                      ·
                        rfl

theorem cell23_6814256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 1, 3].length) (baseStart_6814256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814256 prefixEnd_6814256 := by exact prefixLift 6814256
  have htrace : WordTrace (prefixWord ++ tailWord_6814256) baseStart_6814256 baseEnd_6814256 := by
    simpa [prefixWord, tailWord_6814256, baseEnd_6814256] using wordTrace_append hprefix tailTrace_6814256
  have hstable : (prefixWord ++ tailWord_6814256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814256).length < 2 ^ (prefixWord ++ tailWord_6814256).sum := by decide
  have hdescent : baseEnd_6814256 < baseStart_6814256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814289 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_6814289 : Nat := 118140960795 + 6814289 * 2 ^ 59
def prefixEnd_6814289 : Nat := 4983230072969 + 3 ^ 40 * 6814289 * 2
def baseEnd_6814289 : Nat := 1166335191881864932216387

theorem tailTrace_6814289 : CollatzResearch.WordTrace tailWord_6814289 prefixEnd_6814289 1166335191881864932216387 := by
  unfold tailWord_6814289
  simp only [CollatzResearch.WordTrace]
  refine ⟨248537538010002215752421921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165691692006668143834947947 248537538010002215752421921)
  ·
    refine ⟨186403153507501661814316441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248537538010002215752421921 186403153507501661814316441)
    ·
      refine ⟨139802365130626246360737331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186403153507501661814316441 139802365130626246360737331)
      ·
        refine ⟨209703547695939369541105997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139802365130626246360737331 209703547695939369541105997)
        ·
          refine ⟨78638830385977263577914749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209703547695939369541105997 78638830385977263577914749)
          ·
            refine ⟨29489561394741473841718031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78638830385977263577914749 29489561394741473841718031)
            ·
              refine ⟨44234342092112210762577047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29489561394741473841718031 44234342092112210762577047)
              ·
                refine ⟨66351513138168316143865571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44234342092112210762577047 66351513138168316143865571)
                ·
                  refine ⟨99527269707252474215798357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66351513138168316143865571 99527269707252474215798357)
                  ·
                    refine ⟨1166335191881864932216387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99527269707252474215798357 1166335191881864932216387)
                    ·
                      rfl

theorem cell23_6814289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_6814289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814289 prefixEnd_6814289 := by exact prefixLift 6814289
  have htrace : WordTrace (prefixWord ++ tailWord_6814289) baseStart_6814289 baseEnd_6814289 := by
    simpa [prefixWord, tailWord_6814289, baseEnd_6814289] using wordTrace_append hprefix tailTrace_6814289
  have hstable : (prefixWord ++ tailWord_6814289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814289).length < 2 ^ (prefixWord ++ tailWord_6814289).sum := by decide
  have hdescent : baseEnd_6814289 < baseStart_6814289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814313 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 4, 2, 2]
def baseStart_6814313 : Nat := 118140960795 + 6814313 * 2 ^ 59
def prefixEnd_6814313 : Nat := 4983230072969 + 3 ^ 40 * 6814313 * 2
def baseEnd_6814313 : Nat := 3499017899181302702749051

theorem tailTrace_6814313 : CollatzResearch.WordTrace tailWord_6814313 prefixEnd_6814313 3499017899181302702749051 := by
  unfold tailWord_6814313
  simp only [CollatzResearch.WordTrace]
  refine ⟨248538413361915267851295593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165692275574610178567530395 248538413361915267851295593)
  ·
    refine ⟨186403810021436450888471695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248538413361915267851295593 186403810021436450888471695)
    ·
      refine ⟨279605715032154676332707543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186403810021436450888471695 279605715032154676332707543)
      ·
        refine ⟨419408572548232014499061315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279605715032154676332707543 419408572548232014499061315)
        ·
          refine ⟨629112858822348021748591973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419408572548232014499061315 629112858822348021748591973)
          ·
            refine ⟨117958661029190254077860995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 629112858822348021748591973 117958661029190254077860995)
            ·
              refine ⟨176937991543785381116791493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117958661029190254077860995 176937991543785381116791493)
              ·
                refine ⟨33175873414459758959398405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176937991543785381116791493 33175873414459758959398405)
                ·
                  refine ⟨6220476265211204804887201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33175873414459758959398405 6220476265211204804887201)
                  ·
                    refine ⟨4665357198908403603665401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220476265211204804887201 4665357198908403603665401)
                    ·
                      refine ⟨3499017899181302702749051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665357198908403603665401 3499017899181302702749051)
                      ·
                        rfl

theorem cell23_6814313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 2, 2].length) (baseStart_6814313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814313 prefixEnd_6814313 := by exact prefixLift 6814313
  have htrace : WordTrace (prefixWord ++ tailWord_6814313) baseStart_6814313 baseEnd_6814313 := by
    simpa [prefixWord, tailWord_6814313, baseEnd_6814313] using wordTrace_append hprefix tailTrace_6814313
  have hstable : (prefixWord ++ tailWord_6814313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814313).length < 2 ^ (prefixWord ++ tailWord_6814313).sum := by decide
  have hdescent : baseEnd_6814313 < baseStart_6814313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814317 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_6814317 : Nat := 118140960795 + 6814317 * 2 ^ 59
def prefixEnd_6814317 : Nat := 4983230072969 + 3 ^ 40 * 6814317 * 2
def baseEnd_6814317 : Nat := 3499019953103920687099033

theorem tailTrace_6814317 : CollatzResearch.WordTrace tailWord_6814317 prefixEnd_6814317 3499019953103920687099033 := by
  unfold tailWord_6814317
  simp only [CollatzResearch.WordTrace]
  refine ⟨248538559253900776534441205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165692372835933851022960803 248538559253900776534441205)
  ·
    refine ⟨23300489930053197800103863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248538559253900776534441205 23300489930053197800103863)
    ·
      refine ⟨34950734895079796700155795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23300489930053197800103863 34950734895079796700155795)
      ·
        refine ⟨52426102342619695050233693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34950734895079796700155795 52426102342619695050233693)
        ·
          refine ⟨19659788378482385643837635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52426102342619695050233693 19659788378482385643837635)
          ·
            refine ⟨29489682567723578465756453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19659788378482385643837635 29489682567723578465756453)
            ·
              refine ⟨5529315481448170962329335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29489682567723578465756453 5529315481448170962329335)
              ·
                refine ⟨8293973222172256443494003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529315481448170962329335 8293973222172256443494003)
                ·
                  refine ⟨12440959833258384665241005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8293973222172256443494003 12440959833258384665241005)
                  ·
                    refine ⟨4665359937471894249465377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12440959833258384665241005 4665359937471894249465377)
                    ·
                      refine ⟨3499019953103920687099033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665359937471894249465377 3499019953103920687099033)
                      ·
                        rfl

theorem cell23_6814317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_6814317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814317 prefixEnd_6814317 := by exact prefixLift 6814317
  have htrace : WordTrace (prefixWord ++ tailWord_6814317) baseStart_6814317 baseEnd_6814317 := by
    simpa [prefixWord, tailWord_6814317, baseEnd_6814317] using wordTrace_append hprefix tailTrace_6814317
  have hstable : (prefixWord ++ tailWord_6814317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814317).length < 2 ^ (prefixWord ++ tailWord_6814317).sum := by decide
  have hdescent : baseEnd_6814317 < baseStart_6814317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814336 : List Nat := [2, 1, 1, 2, 1, 6, 2, 1, 7]
def baseStart_6814336 : Nat := 118140960795 + 6814336 * 2 ^ 59
def prefixEnd_6814336 : Nat := 4983230072969 + 3 ^ 40 * 6814336 * 2
def baseEnd_6814336 : Nat := 388781078804039568084605

theorem tailTrace_6814336 : CollatzResearch.WordTrace tailWord_6814336 prefixEnd_6814336 388781078804039568084605 := by
  unfold tailWord_6814336
  simp only [CollatzResearch.WordTrace]
  refine ⟨124269626120415971389691431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165692834827221295186255241 124269626120415971389691431)
  ·
    refine ⟨186404439180623957084537147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124269626120415971389691431 186404439180623957084537147)
    ·
      refine ⟨279606658770935935626805721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186404439180623957084537147 279606658770935935626805721)
      ·
        refine ⟨209704994078201951720104291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279606658770935935626805721 209704994078201951720104291)
        ·
          refine ⟨314557491117302927580156437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209704994078201951720104291 314557491117302927580156437)
          ·
            refine ⟨14744882396123574730319833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314557491117302927580156437 14744882396123574730319833)
            ·
              refine ⟨11058661797092681047739875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14744882396123574730319833 11058661797092681047739875)
              ·
                refine ⟨16587992695639021571609813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11058661797092681047739875 16587992695639021571609813)
                ·
                  refine ⟨388781078804039568084605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16587992695639021571609813 388781078804039568084605)
                  ·
                    rfl

theorem cell23_6814336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 7].length) (baseStart_6814336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814336 prefixEnd_6814336 := by exact prefixLift 6814336
  have htrace : WordTrace (prefixWord ++ tailWord_6814336) baseStart_6814336 baseEnd_6814336 := by
    simpa [prefixWord, tailWord_6814336, baseEnd_6814336] using wordTrace_append hprefix tailTrace_6814336
  have hstable : (prefixWord ++ tailWord_6814336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814336).length < 2 ^ (prefixWord ++ tailWord_6814336).sum := by decide
  have hdescent : baseEnd_6814336 < baseStart_6814336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814423 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_6814423 : Nat := 118140960795 + 6814423 * 2 ^ 59
def prefixEnd_6814423 : Nat := 4983230072969 + 3 ^ 40 * 6814423 * 2
def baseEnd_6814423 : Nat := 3499074382053297272373545

theorem tailTrace_6814423 : CollatzResearch.WordTrace tailWord_6814423 prefixEnd_6814423 3499074382053297272373545 := by
  unfold tailWord_6814423
  simp only [CollatzResearch.WordTrace]
  refine ⟨248542425391516756637799923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165694950261011171091866615 248542425391516756637799923)
  ·
    refine ⟨372813638087275134956699885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248542425391516756637799923 372813638087275134956699885)
    ·
      refine ⟨139805114282728175608762457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372813638087275134956699885 139805114282728175608762457)
      ·
        refine ⟨104853835712046131706571843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139805114282728175608762457 104853835712046131706571843)
        ·
          refine ⟨157280753568069197559857765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104853835712046131706571843 157280753568069197559857765)
          ·
            refine ⟨29490141294012974542473331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157280753568069197559857765 29490141294012974542473331)
            ·
              refine ⟨44235211941019461813709997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29490141294012974542473331 44235211941019461813709997)
              ·
                refine ⟨16588204477882298180141249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44235211941019461813709997 16588204477882298180141249)
                ·
                  refine ⟨12441153358411723635105937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16588204477882298180141249 12441153358411723635105937)
                  ·
                    refine ⟨9330865018808792726329453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12441153358411723635105937 9330865018808792726329453)
                    ·
                      refine ⟨3499074382053297272373545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9330865018808792726329453 3499074382053297272373545)
                      ·
                        rfl

theorem cell23_6814423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_6814423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814423 prefixEnd_6814423 := by exact prefixLift 6814423
  have htrace : WordTrace (prefixWord ++ tailWord_6814423) baseStart_6814423 baseEnd_6814423 := by
    simpa [prefixWord, tailWord_6814423, baseEnd_6814423] using wordTrace_append hprefix tailTrace_6814423
  have hstable : (prefixWord ++ tailWord_6814423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814423).length < 2 ^ (prefixWord ++ tailWord_6814423).sum := by decide
  have hdescent : baseEnd_6814423 < baseStart_6814423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814447 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 1, 4]
def baseStart_6814447 : Nat := 118140960795 + 6814447 * 2 ^ 59
def prefixEnd_6814447 : Nat := 4983230072969 + 3 ^ 40 * 6814447 * 2
def baseEnd_6814447 : Nat := 1166362235196335059491145

theorem tailTrace_6814447 : CollatzResearch.WordTrace tailWord_6814447 prefixEnd_6814447 1166362235196335059491145 := by
  unfold tailWord_6814447
  simp only [CollatzResearch.WordTrace]
  refine ⟨248543300743429808736673595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165695533828953205824449063 248543300743429808736673595)
  ·
    refine ⟨372814951115144713105010393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248543300743429808736673595 372814951115144713105010393)
    ·
      refine ⟨279611213336358534828757795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372814951115144713105010393 279611213336358534828757795)
      ·
        refine ⟨419416820004537802243136693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279611213336358534828757795 419416820004537802243136693)
        ·
          refine ⟨39320326875425418960294065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 419416820004537802243136693 39320326875425418960294065)
          ·
            refine ⟨29490245156569064220220549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39320326875425418960294065 29490245156569064220220549)
            ·
              refine ⟨5529420966856699541291353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29490245156569064220220549 5529420966856699541291353)
              ·
                refine ⟨4147065725142524655968515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529420966856699541291353 4147065725142524655968515)
                ·
                  refine ⟨6220598587713786983952773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147065725142524655968515 6220598587713786983952773)
                  ·
                    refine ⟨1166362235196335059491145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220598587713786983952773 1166362235196335059491145)
                    ·
                      rfl

theorem cell23_6814447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 1, 4].length) (baseStart_6814447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814447 prefixEnd_6814447 := by exact prefixLift 6814447
  have htrace : WordTrace (prefixWord ++ tailWord_6814447) baseStart_6814447 baseEnd_6814447 := by
    simpa [prefixWord, tailWord_6814447, baseEnd_6814447] using wordTrace_append hprefix tailTrace_6814447
  have hstable : (prefixWord ++ tailWord_6814447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814447).length < 2 ^ (prefixWord ++ tailWord_6814447).sum := by decide
  have hdescent : baseEnd_6814447 < baseStart_6814447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814456 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 5, 5]
def baseStart_6814456 : Nat := 118140960795 + 6814456 * 2 ^ 59
def prefixEnd_6814456 : Nat := 4983230072969 + 3 ^ 40 * 6814456 * 2
def baseEnd_6814456 : Nat := 1166363775638298547753631

theorem tailTrace_6814456 : CollatzResearch.WordTrace tailWord_6814456 prefixEnd_6814456 1166363775638298547753631 := by
  unfold tailWord_6814456
  simp only [CollatzResearch.WordTrace]
  refine ⟨124271814500198601636875611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165695752666931468849167481 124271814500198601636875611)
  ·
    refine ⟨186407721750297902455313417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124271814500198601636875611 186407721750297902455313417)
    ·
      refine ⟨139805791312723426841485063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186407721750297902455313417 139805791312723426841485063)
      ·
        refine ⟨209708686969085140262227595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139805791312723426841485063 209708686969085140262227595)
        ·
          refine ⟨314563030453627710393341393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209708686969085140262227595 314563030453627710393341393)
          ·
            refine ⟨235922272840220782795006045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314563030453627710393341393 235922272840220782795006045)
            ·
              refine ⟨88470852315082793548127267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235922272840220782795006045 88470852315082793548127267)
              ·
                refine ⟨132706278472624190322190901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88470852315082793548127267 132706278472624190322190901)
                ·
                  refine ⟨12441213606808517842705397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132706278472624190322190901 12441213606808517842705397)
                  ·
                    refine ⟨1166363775638298547753631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12441213606808517842705397 1166363775638298547753631)
                    ·
                      rfl

theorem cell23_6814456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_6814456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814456 prefixEnd_6814456 := by exact prefixLift 6814456
  have htrace : WordTrace (prefixWord ++ tailWord_6814456) baseStart_6814456 baseEnd_6814456 := by
    simpa [prefixWord, tailWord_6814456, baseEnd_6814456] using wordTrace_append hprefix tailTrace_6814456
  have hstable : (prefixWord ++ tailWord_6814456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814456).length < 2 ^ (prefixWord ++ tailWord_6814456).sum := by decide
  have hdescent : baseEnd_6814456 < baseStart_6814456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814463 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 1, 5, 2]
def baseStart_6814463 : Nat := 118140960795 + 6814463 * 2 ^ 59
def prefixEnd_6814463 : Nat := 4983230072969 + 3 ^ 40 * 6814463 * 2
def baseEnd_6814463 : Nat := 3499094921279477115873361

theorem tailTrace_6814463 : CollatzResearch.WordTrace tailWord_6814463 prefixEnd_6814463 3499094921279477115873361 := by
  unfold tailWord_6814463
  simp only [CollatzResearch.WordTrace]
  refine ⟨248543884311371843469256043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165695922874247895646170695 248543884311371843469256043)
  ·
    refine ⟨372815826467057765203884065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248543884311371843469256043 372815826467057765203884065)
    ·
      refine ⟨279611869850293323902913049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372815826467057765203884065 279611869850293323902913049)
      ·
        refine ⟨209708902387719992927184787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279611869850293323902913049 209708902387719992927184787)
        ·
          refine ⟨314563353581579989390777181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209708902387719992927184787 314563353581579989390777181)
          ·
            refine ⟨117961257593092496021541443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314563353581579989390777181 117961257593092496021541443)
            ·
              refine ⟨176941886389638744032312165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117961257593092496021541443 176941886389638744032312165)
              ·
                refine ⟨33176603698057264506058531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176941886389638744032312165 33176603698057264506058531)
                ·
                  refine ⟨49764905547085896759087797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33176603698057264506058531 49764905547085896759087797)
                  ·
                    refine ⟨4665459895039302821164481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49764905547085896759087797 4665459895039302821164481)
                    ·
                      refine ⟨3499094921279477115873361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665459895039302821164481 3499094921279477115873361)
                      ·
                        rfl

theorem cell23_6814463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5, 2].length) (baseStart_6814463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814463 prefixEnd_6814463 := by exact prefixLift 6814463
  have htrace : WordTrace (prefixWord ++ tailWord_6814463) baseStart_6814463 baseEnd_6814463 := by
    simpa [prefixWord, tailWord_6814463, baseEnd_6814463] using wordTrace_append hprefix tailTrace_6814463
  have hstable : (prefixWord ++ tailWord_6814463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814463).length < 2 ^ (prefixWord ++ tailWord_6814463).sum := by decide
  have hdescent : baseEnd_6814463 < baseStart_6814463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814513 : List Nat := [1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_6814513 : Nat := 118140960795 + 6814513 * 2 ^ 59
def prefixEnd_6814513 : Nat := 4983230072969 + 3 ^ 40 * 6814513 * 2
def baseEnd_6814513 : Nat := 3499120595312201920248131

theorem tailTrace_6814513 : CollatzResearch.WordTrace tailWord_6814513 prefixEnd_6814513 3499120595312201920248131 := by
  unfold tailWord_6814513
  simp only [CollatzResearch.WordTrace]
  refine ⟨248545707961190702008576193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165697138640793801339050795 248545707961190702008576193)
  ·
    refine ⟨186409280970893026506432145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248545707961190702008576193 186409280970893026506432145)
    ·
      refine ⟨139806960728169769879824109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186409280970893026506432145 139806960728169769879824109)
      ·
        refine ⟨52427610273063663704934041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139806960728169769879824109 52427610273063663704934041)
        ·
          refine ⟨39320707704797747778700531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52427610273063663704934041 39320707704797747778700531)
          ·
            refine ⟨58981061557196621668050797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39320707704797747778700531 58981061557196621668050797)
            ·
              refine ⟨22117898083948733125519049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58981061557196621668050797 22117898083948733125519049)
              ·
                refine ⟨16588423562961549844139287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22117898083948733125519049 16588423562961549844139287)
                ·
                  refine ⟨24882635344442324766208931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16588423562961549844139287 24882635344442324766208931)
                  ·
                    refine ⟨37323953016663487149313397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24882635344442324766208931 37323953016663487149313397)
                    ·
                      refine ⟨3499120595312201920248131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37323953016663487149313397 3499120595312201920248131)
                      ·
                        rfl

theorem cell23_6814513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_6814513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814513 prefixEnd_6814513 := by exact prefixLift 6814513
  have htrace : WordTrace (prefixWord ++ tailWord_6814513) baseStart_6814513 baseEnd_6814513 := by
    simpa [prefixWord, tailWord_6814513, baseEnd_6814513] using wordTrace_append hprefix tailTrace_6814513
  have hstable : (prefixWord ++ tailWord_6814513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814513).length < 2 ^ (prefixWord ++ tailWord_6814513).sum := by decide
  have hdescent : baseEnd_6814513 < baseStart_6814513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814527 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 3, 2, 2]
def baseStart_6814527 : Nat := 118140960795 + 6814527 * 2 ^ 59
def prefixEnd_6814527 : Nat := 4983230072969 + 3 ^ 40 * 6814527 * 2
def baseEnd_6814527 : Nat := 3499127784041364865473067

theorem tailTrace_6814527 : CollatzResearch.WordTrace tailWord_6814527 prefixEnd_6814527 3499127784041364865473067 := by
  unfold tailWord_6814527
  simp only [CollatzResearch.WordTrace]
  refine ⟨248546218583139982399585835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165697479055426654933057223 248546218583139982399585835)
  ·
    refine ⟨372819327874709973599378753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248546218583139982399585835 372819327874709973599378753)
    ·
      refine ⟨279614495906032480199534065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372819327874709973599378753 279614495906032480199534065)
      ·
        refine ⟨209710871929524360149650549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279614495906032480199534065 209710871929524360149650549)
        ·
          refine ⟨19660394243392908764029739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209710871929524360149650549 19660394243392908764029739)
          ·
            refine ⟨29490591365089363146044609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19660394243392908764029739 29490591365089363146044609)
            ·
              refine ⟨22117943523817022359533457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29490591365089363146044609 22117943523817022359533457)
              ·
                refine ⟨16588457642862766769650093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22117943523817022359533457 16588457642862766769650093)
                ·
                  refine ⟨6220671616073537538618785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16588457642862766769650093 6220671616073537538618785)
                  ·
                    refine ⟨4665503712055153153964089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220671616073537538618785 4665503712055153153964089)
                    ·
                      refine ⟨3499127784041364865473067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665503712055153153964089 3499127784041364865473067)
                      ·
                        rfl

theorem cell23_6814527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 2, 2].length) (baseStart_6814527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814527 prefixEnd_6814527 := by exact prefixLift 6814527
  have htrace : WordTrace (prefixWord ++ tailWord_6814527) baseStart_6814527 baseEnd_6814527 := by
    simpa [prefixWord, tailWord_6814527, baseEnd_6814527] using wordTrace_append hprefix tailTrace_6814527
  have hstable : (prefixWord ++ tailWord_6814527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814527).length < 2 ^ (prefixWord ++ tailWord_6814527).sum := by decide
  have hdescent : baseEnd_6814527 < baseStart_6814527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814544 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 1, 2, 2]
def baseStart_6814544 : Nat := 118140960795 + 6814544 * 2 ^ 59
def prefixEnd_6814544 : Nat := 4983230072969 + 3 ^ 40 * 6814544 * 2
def baseEnd_6814544 : Nat := 3499136513212491298960489

theorem tailTrace_6814544 : CollatzResearch.WordTrace tailWord_6814544 prefixEnd_6814544 3499136513212491298960489 := by
  unfold tailWord_6814544
  simp only [CollatzResearch.WordTrace]
  refine ⟨124273419312039197151477343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165697892416052262868636457 124273419312039197151477343)
  ·
    refine ⟨186410128968058795727216015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124273419312039197151477343 186410128968058795727216015)
    ·
      refine ⟨279615193452088193590824023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186410128968058795727216015 279615193452088193590824023)
      ·
        refine ⟨419422790178132290386236035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279615193452088193590824023 419422790178132290386236035)
        ·
          refine ⟨629134185267198435579354053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419422790178132290386236035 629134185267198435579354053)
          ·
            refine ⟨117962659737599706671128885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 629134185267198435579354053 117962659737599706671128885)
            ·
              refine ⟨11058999350399972500418333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117962659737599706671128885 11058999350399972500418333)
              ·
                refine ⟨4147124756399989687656875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11058999350399972500418333 4147124756399989687656875)
                ·
                  refine ⟨6220687134599984531485313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147124756399989687656875 6220687134599984531485313)
                  ·
                    refine ⟨4665515350949988398613985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220687134599984531485313 4665515350949988398613985)
                    ·
                      refine ⟨3499136513212491298960489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665515350949988398613985 3499136513212491298960489)
                      ·
                        rfl

theorem cell23_6814544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 2, 2].length) (baseStart_6814544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814544 prefixEnd_6814544 := by exact prefixLift 6814544
  have htrace : WordTrace (prefixWord ++ tailWord_6814544) baseStart_6814544 baseEnd_6814544 := by
    simpa [prefixWord, tailWord_6814544, baseEnd_6814544] using wordTrace_append hprefix tailTrace_6814544
  have hstable : (prefixWord ++ tailWord_6814544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814544).length < 2 ^ (prefixWord ++ tailWord_6814544).sum := by decide
  have hdescent : baseEnd_6814544 < baseStart_6814544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814560 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 4, 1, 3]
def baseStart_6814560 : Nat := 118140960795 + 6814560 * 2 ^ 59
def prefixEnd_6814560 : Nat := 4983230072969 + 3 ^ 40 * 6814560 * 2
def baseEnd_6814560 : Nat := 3499144728902963236360415

theorem tailTrace_6814560 : CollatzResearch.WordTrace tailWord_6814560 prefixEnd_6814560 3499144728902963236360415 := by
  unfold tailWord_6814560
  simp only [CollatzResearch.WordTrace]
  refine ⟨124273711096010214517768567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165698281461346952690358089 124273711096010214517768567)
  ·
    refine ⟨186410566644015321776652851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124273711096010214517768567 186410566644015321776652851)
    ·
      refine ⟨279615849966022982664979277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186410566644015321776652851 279615849966022982664979277)
      ·
        refine ⟨104855943737258618499367229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279615849966022982664979277 104855943737258618499367229)
        ·
          refine ⟨39320978901471981937262711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104855943737258618499367229 39320978901471981937262711)
          ·
            refine ⟨58981468352207972905894067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39320978901471981937262711 58981468352207972905894067)
            ·
              refine ⟨88472202528311959358841101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58981468352207972905894067 88472202528311959358841101)
              ·
                refine ⟨33177075948116984759565413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88472202528311959358841101 33177075948116984759565413)
                ·
                  refine ⟨6220701740271934642418515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33177075948116984759565413 6220701740271934642418515)
                  ·
                    refine ⟨9331052610407901963627773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220701740271934642418515 9331052610407901963627773)
                    ·
                      refine ⟨3499144728902963236360415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331052610407901963627773 3499144728902963236360415)
                      ·
                        rfl

theorem cell23_6814560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_6814560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814560 prefixEnd_6814560 := by exact prefixLift 6814560
  have htrace : WordTrace (prefixWord ++ tailWord_6814560) baseStart_6814560 baseEnd_6814560 := by
    simpa [prefixWord, tailWord_6814560, baseEnd_6814560] using wordTrace_append hprefix tailTrace_6814560
  have hstable : (prefixWord ++ tailWord_6814560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814560).length < 2 ^ (prefixWord ++ tailWord_6814560).sum := by decide
  have hdescent : baseEnd_6814560 < baseStart_6814560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814577 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_6814577 : Nat := 118140960795 + 6814577 * 2 ^ 59
def prefixEnd_6814577 : Nat := 4983230072969 + 3 ^ 40 * 6814577 * 2
def baseEnd_6814577 : Nat := 3499153458074089669847837

theorem tailTrace_6814577 : CollatzResearch.WordTrace tailWord_6814577 prefixEnd_6814577 3499153458074089669847837 := by
  unfold tailWord_6814577
  simp only [CollatzResearch.WordTrace]
  refine ⟨248548042232958840938905985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165698694821972560625937323 248548042232958840938905985)
  ·
    refine ⟨186411031674719130704179489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248548042232958840938905985 186411031674719130704179489)
    ·
      refine ⟨139808273756039348028134617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186411031674719130704179489 139808273756039348028134617)
      ·
        refine ⟨104856205317029511021100963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139808273756039348028134617 104856205317029511021100963)
        ·
          refine ⟨157284307975544266531651445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104856205317029511021100963 157284307975544266531651445)
          ·
            refine ⟨14745403872707274987342323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157284307975544266531651445 14745403872707274987342323)
            ·
              refine ⟨22118105809060912481013485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14745403872707274987342323 22118105809060912481013485)
              ·
                refine ⟨8294289678397842180380057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22118105809060912481013485 8294289678397842180380057)
                ·
                  refine ⟨6220717258798381635285043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294289678397842180380057 6220717258798381635285043)
                  ·
                    refine ⟨9331075888197572452927565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220717258798381635285043 9331075888197572452927565)
                    ·
                      refine ⟨3499153458074089669847837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331075888197572452927565 3499153458074089669847837)
                      ·
                        rfl

theorem cell23_6814577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_6814577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814577 prefixEnd_6814577 := by exact prefixLift 6814577
  have htrace : WordTrace (prefixWord ++ tailWord_6814577) baseStart_6814577 baseEnd_6814577 := by
    simpa [prefixWord, tailWord_6814577, baseEnd_6814577] using wordTrace_append hprefix tailTrace_6814577
  have hstable : (prefixWord ++ tailWord_6814577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814577).length < 2 ^ (prefixWord ++ tailWord_6814577).sum := by decide
  have hdescent : baseEnd_6814577 < baseStart_6814577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814587 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 1, 3, 2]
def baseStart_6814587 : Nat := 118140960795 + 6814587 * 2 ^ 59
def prefixEnd_6814587 : Nat := 4983230072969 + 3 ^ 40 * 6814587 * 2
def baseEnd_6814587 : Nat := 3499158592880634630722791

theorem tailTrace_6814587 : CollatzResearch.WordTrace tailWord_6814587 prefixEnd_6814587 3499158592880634630722791 := by
  unfold tailWord_6814587
  simp only [CollatzResearch.WordTrace]
  refine ⟨248548406962922612646770015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165698937975281741764513343 248548406962922612646770015)
  ·
    refine ⟨372822610444383918970155023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248548406962922612646770015 372822610444383918970155023)
    ·
      refine ⟨559233915666575878455232535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372822610444383918970155023 559233915666575878455232535)
      ·
        refine ⟨838850873499863817682848803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559233915666575878455232535 838850873499863817682848803)
        ·
          refine ⟨1258276310249795726524273205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838850873499863817682848803 1258276310249795726524273205)
          ·
            refine ⟨117963404085918349361650613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1258276310249795726524273205 117963404085918349361650613)
            ·
              refine ⟨11059069133054845252654745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117963404085918349361650613 11059069133054845252654745)
              ·
                refine ⟨8294301849791133939491059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11059069133054845252654745 8294301849791133939491059)
                ·
                  refine ⟨12441452774686700909236589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294301849791133939491059 12441452774686700909236589)
                  ·
                    refine ⟨4665544790507512840963721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12441452774686700909236589 4665544790507512840963721)
                    ·
                      refine ⟨3499158592880634630722791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665544790507512840963721 3499158592880634630722791)
                      ·
                        rfl

theorem cell23_6814587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 3, 2].length) (baseStart_6814587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814587 prefixEnd_6814587 := by exact prefixLift 6814587
  have htrace : WordTrace (prefixWord ++ tailWord_6814587) baseStart_6814587 baseEnd_6814587 := by
    simpa [prefixWord, tailWord_6814587, baseEnd_6814587] using wordTrace_append hprefix tailTrace_6814587
  have hstable : (prefixWord ++ tailWord_6814587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814587).length < 2 ^ (prefixWord ++ tailWord_6814587).sum := by decide
  have hdescent : baseEnd_6814587 < baseStart_6814587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814603 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5]
def baseStart_6814603 : Nat := 118140960795 + 6814603 * 2 ^ 59
def prefixEnd_6814603 : Nat := 4983230072969 + 3 ^ 40 * 6814603 * 2
def baseEnd_6814603 : Nat := 3499166808571106568122717

theorem tailTrace_6814603 : CollatzResearch.WordTrace tailWord_6814603 prefixEnd_6814603 3499166808571106568122717 := by
  unfold tailWord_6814603
  simp only [CollatzResearch.WordTrace]
  refine ⟨248548990530864647379352463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165699327020576431586234975 248548990530864647379352463)
  ·
    refine ⟨372823485796296971069028695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248548990530864647379352463 372823485796296971069028695)
    ·
      refine ⟨559235228694445456603543043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372823485796296971069028695 559235228694445456603543043)
      ·
        refine ⟨838852843041668184905314565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559235228694445456603543043 838852843041668184905314565)
        ·
          refine ⟨157284908070312784669746481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 838852843041668184905314565 157284908070312784669746481)
          ·
            refine ⟨117963681052734588502309861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157284908070312784669746481 117963681052734588502309861)
            ·
              refine ⟨22118190197387735344183099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117963681052734588502309861 22118190197387735344183099)
              ·
                refine ⟨33177285296081603016274649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22118190197387735344183099 33177285296081603016274649)
                ·
                  refine ⟨24882963972061202262205987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33177285296081603016274649 24882963972061202262205987)
                  ·
                    refine ⟨37324445958091803393308981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24882963972061202262205987 37324445958091803393308981)
                    ·
                      refine ⟨3499166808571106568122717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37324445958091803393308981 3499166808571106568122717)
                      ·
                        rfl

theorem cell23_6814603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_6814603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814603 prefixEnd_6814603 := by exact prefixLift 6814603
  have htrace : WordTrace (prefixWord ++ tailWord_6814603) baseStart_6814603 baseEnd_6814603 := by
    simpa [prefixWord, tailWord_6814603, baseEnd_6814603] using wordTrace_append hprefix tailTrace_6814603
  have hstable : (prefixWord ++ tailWord_6814603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814603).length < 2 ^ (prefixWord ++ tailWord_6814603).sum := by decide
  have hdescent : baseEnd_6814603 < baseStart_6814603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814662 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_6814662 : Nat := 118140960795 + 6814662 * 2 ^ 59
def prefixEnd_6814662 : Nat := 4983230072969 + 3 ^ 40 * 6814662 * 2
def baseEnd_6814662 : Nat := 3499197103929721837284947

theorem tailTrace_6814662 : CollatzResearch.WordTrace tailWord_6814662 prefixEnd_6814662 3499197103929721837284947 := by
  unfold tailWord_6814662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767223201176590639242195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165700761625100600303833493 7767223201176590639242195)
  ·
    refine ⟨11650834801764885958863293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767223201176590639242195 11650834801764885958863293)
    ·
      refine ⟨4369063050661832234573735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11650834801764885958863293 4369063050661832234573735)
      ·
        refine ⟨6553594575992748351860603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369063050661832234573735 6553594575992748351860603)
        ·
          refine ⟨9830391863989122527790905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553594575992748351860603 9830391863989122527790905)
          ·
            refine ⟨7372793897991841895843179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9830391863989122527790905 7372793897991841895843179)
            ·
              refine ⟨11059190846987762843764769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372793897991841895843179 11059190846987762843764769)
              ·
                refine ⟨8294393135240822132823577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11059190846987762843764769 8294393135240822132823577)
                ·
                  refine ⟨6220794851430616599617683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294393135240822132823577 6220794851430616599617683)
                  ·
                    refine ⟨9331192277145924899426525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220794851430616599617683 9331192277145924899426525)
                    ·
                      refine ⟨3499197103929721837284947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331192277145924899426525 3499197103929721837284947)
                      ·
                        rfl

theorem cell23_6814662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_6814662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814662 prefixEnd_6814662 := by exact prefixLift 6814662
  have htrace : WordTrace (prefixWord ++ tailWord_6814662) baseStart_6814662 baseEnd_6814662 := by
    simpa [prefixWord, tailWord_6814662, baseEnd_6814662] using wordTrace_append hprefix tailTrace_6814662
  have hstable : (prefixWord ++ tailWord_6814662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814662).length < 2 ^ (prefixWord ++ tailWord_6814662).sum := by decide
  have hdescent : baseEnd_6814662 < baseStart_6814662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814663 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_6814663 : Nat := 118140960795 + 6814663 * 2 ^ 59
def prefixEnd_6814663 : Nat := 4983230072969 + 3 ^ 40 * 6814663 * 2
def baseEnd_6814663 : Nat := 3499197617410376333372441

theorem tailTrace_6814663 : CollatzResearch.WordTrace tailWord_6814663 prefixEnd_6814663 3499197617410376333372441 := by
  unfold tailWord_6814663
  simp only [CollatzResearch.WordTrace]
  refine ⟨248551178910647277626536643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165700785940431518417691095 248551178910647277626536643)
  ·
    refine ⟨372826768365970916439804965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248551178910647277626536643 372826768365970916439804965)
    ·
      refine ⟨69905019068619546832463431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372826768365970916439804965 69905019068619546832463431)
      ·
        refine ⟨104857528602929320248695147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69905019068619546832463431 104857528602929320248695147)
        ·
          refine ⟨157286292904393980373042721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104857528602929320248695147 157286292904393980373042721)
          ·
            refine ⟨117964719678295485279782041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157286292904393980373042721 117964719678295485279782041)
            ·
              refine ⟨88473539758721613959836531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117964719678295485279782041 88473539758721613959836531)
              ·
                refine ⟨132710309638082420939754797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88473539758721613959836531 132710309638082420939754797)
                ·
                  refine ⟨49766366114280907852408049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132710309638082420939754797 49766366114280907852408049)
                  ·
                    refine ⟨37324774585710680889306037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49766366114280907852408049 37324774585710680889306037)
                    ·
                      refine ⟨3499197617410376333372441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37324774585710680889306037 3499197617410376333372441)
                      ·
                        rfl

theorem cell23_6814663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_6814663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814663 prefixEnd_6814663 := by exact prefixLift 6814663
  have htrace : WordTrace (prefixWord ++ tailWord_6814663) baseStart_6814663 baseEnd_6814663 := by
    simpa [prefixWord, tailWord_6814663, baseEnd_6814663] using wordTrace_append hprefix tailTrace_6814663
  have hstable : (prefixWord ++ tailWord_6814663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814663).length < 2 ^ (prefixWord ++ tailWord_6814663).sum := by decide
  have hdescent : baseEnd_6814663 < baseStart_6814663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814713 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 10]
def baseStart_6814713 : Nat := 118140960795 + 6814713 * 2 ^ 59
def prefixEnd_6814713 : Nat := 4983230072969 + 3 ^ 40 * 6814713 * 2
def baseEnd_6814713 : Nat := 388802587938122348638579

theorem tailTrace_6814713 : CollatzResearch.WordTrace tailWord_6814713 prefixEnd_6814713 388802587938122348638579 := by
  unfold tailWord_6814713
  simp only [CollatzResearch.WordTrace]
  refine ⟨248553002560466136165856793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165702001706977424110571195 248553002560466136165856793)
  ·
    refine ⟨186414751920349602124392595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248553002560466136165856793 186414751920349602124392595)
    ·
      refine ⟨279622127880524403186588893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186414751920349602124392595 279622127880524403186588893)
      ·
        refine ⟨104858297955196651194970835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279622127880524403186588893 104858297955196651194970835)
        ·
          refine ⟨157287446932794976792456253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104858297955196651194970835 157287446932794976792456253)
          ·
            refine ⟨58982792599798116297171095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157287446932794976792456253 58982792599798116297171095)
            ·
              refine ⟨88474188899697174445756643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58982792599798116297171095 88474188899697174445756643)
              ·
                refine ⟨132711283349545761668634965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88474188899697174445756643 132711283349545761668634965)
                ·
                  refine ⟨388802587938122348638579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132711283349545761668634965 388802587938122348638579)
                  ·
                    rfl

theorem cell23_6814713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_6814713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814713 prefixEnd_6814713 := by exact prefixLift 6814713
  have htrace : WordTrace (prefixWord ++ tailWord_6814713) baseStart_6814713 baseEnd_6814713 := by
    simpa [prefixWord, tailWord_6814713, baseEnd_6814713] using wordTrace_append hprefix tailTrace_6814713
  have hstable : (prefixWord ++ tailWord_6814713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814713).length < 2 ^ (prefixWord ++ tailWord_6814713).sum := by decide
  have hdescent : baseEnd_6814713 < baseStart_6814713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814727 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6814727 : Nat := 118140960795 + 6814727 * 2 ^ 59
def prefixEnd_6814727 : Nat := 4983230072969 + 3 ^ 40 * 6814727 * 2
def baseEnd_6814727 : Nat := 3499230480172264082972147

theorem tailTrace_6814727 : CollatzResearch.WordTrace tailWord_6814727 prefixEnd_6814727 3499230480172264082972147 := by
  unfold tailWord_6814727
  simp only [CollatzResearch.WordTrace]
  refine ⟨248553513182415416556866435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165702342121610277704577623 248553513182415416556866435)
  ·
    refine ⟨372830269773623124835299653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248553513182415416556866435 372830269773623124835299653)
    ·
      refine ⟨69905675582554335906618685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372830269773623124835299653 69905675582554335906618685)
      ·
        refine ⟨26214628343457875964982007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69905675582554335906618685 26214628343457875964982007)
        ·
          refine ⟨39321942515186813947473011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26214628343457875964982007 39321942515186813947473011)
          ·
            refine ⟨58982913772780220921209517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39321942515186813947473011 58982913772780220921209517)
            ·
              refine ⟨22118592664792582845453569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58982913772780220921209517 22118592664792582845453569)
              ·
                refine ⟨16588944498594437134090177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22118592664792582845453569 16588944498594437134090177)
                ·
                  refine ⟨12441708373945827850567633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16588944498594437134090177 12441708373945827850567633)
                  ·
                    refine ⟨9331281280459370887925725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12441708373945827850567633 9331281280459370887925725)
                    ·
                      refine ⟨3499230480172264082972147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331281280459370887925725 3499230480172264082972147)
                      ·
                        rfl

theorem cell23_6814727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6814727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814727 prefixEnd_6814727 := by exact prefixLift 6814727
  have htrace : WordTrace (prefixWord ++ tailWord_6814727) baseStart_6814727 baseEnd_6814727 := by
    simpa [prefixWord, tailWord_6814727, baseEnd_6814727] using wordTrace_append hprefix tailTrace_6814727
  have hstable : (prefixWord ++ tailWord_6814727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814727).length < 2 ^ (prefixWord ++ tailWord_6814727).sum := by decide
  have hdescent : baseEnd_6814727 < baseStart_6814727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814730 : List Nat := [3, 1, 2, 2, 3, 1, 2, 1, 8]
def baseStart_6814730 : Nat := 118140960795 + 6814730 * 2 ^ 59
def prefixEnd_6814730 : Nat := 4983230072969 + 3 ^ 40 * 6814730 * 2
def baseEnd_6814730 : Nat := 388803557846025285692737

theorem tailTrace_6814730 : CollatzResearch.WordTrace tailWord_6814730 prefixEnd_6814730 388803557846025285692737 := by
  unfold tailWord_6814730
  simp only [CollatzResearch.WordTrace]
  refine ⟨62138405650351137017306411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165702415067603032046150429 62138405650351137017306411)
  ·
    refine ⟨93207608475526705525959617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62138405650351137017306411 93207608475526705525959617)
    ·
      refine ⟨69905706356645029144469713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93207608475526705525959617 69905706356645029144469713)
      ·
        refine ⟨52429279767483771858352285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69905706356645029144469713 52429279767483771858352285)
        ·
          refine ⟨19660979912806414446882107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52429279767483771858352285 19660979912806414446882107)
          ·
            refine ⟨29491469869209621670323161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19660979912806414446882107 29491469869209621670323161)
            ·
              refine ⟨22118602401907216252742371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29491469869209621670323161 22118602401907216252742371)
              ·
                refine ⟨33177903602860824379113557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22118602401907216252742371 33177903602860824379113557)
                ·
                  refine ⟨388803557846025285692737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33177903602860824379113557 388803557846025285692737)
                  ·
                    rfl

theorem cell23_6814730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_6814730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814730 prefixEnd_6814730 := by exact prefixLift 6814730
  have htrace : WordTrace (prefixWord ++ tailWord_6814730) baseStart_6814730 baseEnd_6814730 := by
    simpa [prefixWord, tailWord_6814730, baseEnd_6814730] using wordTrace_append hprefix tailTrace_6814730
  have hstable : (prefixWord ++ tailWord_6814730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814730).length < 2 ^ (prefixWord ++ tailWord_6814730).sum := by decide
  have hdescent : baseEnd_6814730 < baseStart_6814730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814734 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_6814734 : Nat := 118140960795 + 6814734 * 2 ^ 59
def prefixEnd_6814734 : Nat := 4983230072969 + 3 ^ 40 * 6814734 * 2
def baseEnd_6814734 : Nat := 1166411358178948518528205

theorem tailTrace_6814734 : CollatzResearch.WordTrace tailWord_6814734 prefixEnd_6814734 1166411358178948518528205 := by
  unfold tailWord_6814734
  simp only [CollatzResearch.WordTrace]
  refine ⟨31069221061673757094046407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165702512328926704501580837 31069221061673757094046407)
  ·
    refine ⟨46603831592510635641069611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31069221061673757094046407 46603831592510635641069611)
    ·
      refine ⟨69905747388765953461604417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46603831592510635641069611 69905747388765953461604417)
      ·
        refine ⟨52429310541574465096203313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69905747388765953461604417 52429310541574465096203313)
        ·
          refine ⟨39321982906180848822152485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52429310541574465096203313 39321982906180848822152485)
          ·
            refine ⟨7372871794908909154153591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39321982906180848822152485 7372871794908909154153591)
            ·
              refine ⟨11059307692363363731230387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372871794908909154153591 11059307692363363731230387)
              ·
                refine ⟨16588961538545045596845581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11059307692363363731230387 16588961538545045596845581)
                ·
                  refine ⟨6220860576954392098817093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16588961538545045596845581 6220860576954392098817093)
                  ·
                    refine ⟨1166411358178948518528205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220860576954392098817093 1166411358178948518528205)
                    ·
                      rfl

theorem cell23_6814734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_6814734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814734 prefixEnd_6814734 := by exact prefixLift 6814734
  have htrace : WordTrace (prefixWord ++ tailWord_6814734) baseStart_6814734 baseEnd_6814734 := by
    simpa [prefixWord, tailWord_6814734, baseEnd_6814734] using wordTrace_append hprefix tailTrace_6814734
  have hstable : (prefixWord ++ tailWord_6814734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814734).length < 2 ^ (prefixWord ++ tailWord_6814734).sum := by decide
  have hdescent : baseEnd_6814734 < baseStart_6814734 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814757 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_6814757 : Nat := 118140960795 + 6814757 * 2 ^ 59
def prefixEnd_6814757 : Nat := 4983230072969 + 3 ^ 40 * 6814757 * 2
def baseEnd_6814757 : Nat := 3499245884591898965597009

theorem tailTrace_6814757 : CollatzResearch.WordTrace tailWord_6814757 prefixEnd_6814757 3499245884591898965597009 := by
  unfold tailWord_6814757
  simp only [CollatzResearch.WordTrace]
  refine ⟨248554607372306731680458525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165703071581537821120305683 248554607372306731680458525)
  ·
    refine ⟨93207977764615024380171947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248554607372306731680458525 93207977764615024380171947)
    ·
      refine ⟨139811966646922536570257921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93207977764615024380171947 139811966646922536570257921)
      ·
        refine ⟨104858974985191902427693441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139811966646922536570257921 104858974985191902427693441)
        ·
          refine ⟨78644231238893926820770081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104858974985191902427693441 78644231238893926820770081)
          ·
            refine ⟨58983173429170445115577561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78644231238893926820770081 58983173429170445115577561)
            ·
              refine ⟨44237380071877833836683171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58983173429170445115577561 44237380071877833836683171)
              ·
                refine ⟨66356070107816750755024757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44237380071877833836683171 66356070107816750755024757)
                ·
                  refine ⟨6220881572607820383283571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66356070107816750755024757 6220881572607820383283571)
                  ·
                    refine ⟨9331322358911730574925357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220881572607820383283571 9331322358911730574925357)
                    ·
                      refine ⟨3499245884591898965597009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331322358911730574925357 3499245884591898965597009)
                      ·
                        rfl

theorem cell23_6814757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_6814757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814757 prefixEnd_6814757 := by exact prefixLift 6814757
  have htrace : WordTrace (prefixWord ++ tailWord_6814757) baseStart_6814757 baseEnd_6814757 := by
    simpa [prefixWord, tailWord_6814757, baseEnd_6814757] using wordTrace_append hprefix tailTrace_6814757
  have hstable : (prefixWord ++ tailWord_6814757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814757).length < 2 ^ (prefixWord ++ tailWord_6814757).sum := by decide
  have hdescent : baseEnd_6814757 < baseStart_6814757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814785 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 1, 4]
def baseStart_6814785 : Nat := 118140960795 + 6814785 * 2 ^ 59
def prefixEnd_6814785 : Nat := 4983230072969 + 3 ^ 40 * 6814785 * 2
def baseEnd_6814785 : Nat := 1166420087350074952015627

theorem tailTrace_6814785 : CollatzResearch.WordTrace tailWord_6814785 prefixEnd_6814785 1166420087350074952015627 := by
  unfold tailWord_6814785
  simp only [CollatzResearch.WordTrace]
  refine ⟨248555628616205292462477809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165703752410803528308318539 248555628616205292462477809)
  ·
    refine ⟨186416721462153969346858357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248555628616205292462477809 186416721462153969346858357)
    ·
      refine ⟨17476567637076934626267971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186416721462153969346858357 17476567637076934626267971)
      ·
        refine ⟨26214851455615401939401957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17476567637076934626267971 26214851455615401939401957)
        ·
          refine ⟨4915284647927887863637867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26214851455615401939401957 4915284647927887863637867)
          ·
            refine ⟨7372926971891831795456801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915284647927887863637867 7372926971891831795456801)
            ·
              refine ⟨5529695228918873846592601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7372926971891831795456801 5529695228918873846592601)
              ·
                refine ⟨4147271421689155384944451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529695228918873846592601 4147271421689155384944451)
                ·
                  refine ⟨6220907132533733077416677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147271421689155384944451 6220907132533733077416677)
                  ·
                    refine ⟨1166420087350074952015627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220907132533733077416677 1166420087350074952015627)
                    ·
                      rfl

theorem cell23_6814785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_6814785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814785 prefixEnd_6814785 := by exact prefixLift 6814785
  have htrace : WordTrace (prefixWord ++ tailWord_6814785) baseStart_6814785 baseEnd_6814785 := by
    simpa [prefixWord, tailWord_6814785, baseEnd_6814785] using wordTrace_append hprefix tailTrace_6814785
  have hstable : (prefixWord ++ tailWord_6814785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814785).length < 2 ^ (prefixWord ++ tailWord_6814785).sum := by decide
  have hdescent : baseEnd_6814785 < baseStart_6814785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814791 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_6814791 : Nat := 118140960795 + 6814791 * 2 ^ 59
def prefixEnd_6814791 : Nat := 4983230072969 + 3 ^ 40 * 6814791 * 2
def baseEnd_6814791 : Nat := 3499263342934151832571853

theorem tailTrace_6814791 : CollatzResearch.WordTrace tailWord_6814791 prefixEnd_6814791 3499263342934151832571853 := by
  unfold tailWord_6814791
  simp only [CollatzResearch.WordTrace]
  refine ⟨248555847454183555487196227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165703898302789036991464151 248555847454183555487196227)
  ·
    refine ⟨372833771181275333230794341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248555847454183555487196227 372833771181275333230794341)
    ·
      refine ⟨69906332096489124980773939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372833771181275333230794341 69906332096489124980773939)
      ·
        refine ⟨104859498144733687471160909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69906332096489124980773939 104859498144733687471160909)
        ·
          refine ⟨39322311804275132801685341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104859498144733687471160909 39322311804275132801685341)
          ·
            refine ⟨14745866926603174800632003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39322311804275132801685341 14745866926603174800632003)
            ·
              refine ⟨22118800389904762200948005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14745866926603174800632003 22118800389904762200948005)
              ·
                refine ⟨4147275073107142912677751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22118800389904762200948005 4147275073107142912677751)
                ·
                  refine ⟨6220912609660714369016627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147275073107142912677751 6220912609660714369016627)
                  ·
                    refine ⟨9331368914491071553524941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6220912609660714369016627 9331368914491071553524941)
                    ·
                      refine ⟨3499263342934151832571853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331368914491071553524941 3499263342934151832571853)
                      ·
                        rfl

theorem cell23_6814791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_6814791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814791 prefixEnd_6814791 := by exact prefixLift 6814791
  have htrace : WordTrace (prefixWord ++ tailWord_6814791) baseStart_6814791 baseEnd_6814791 := by
    simpa [prefixWord, tailWord_6814791, baseEnd_6814791] using wordTrace_append hprefix tailTrace_6814791
  have hstable : (prefixWord ++ tailWord_6814791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814791).length < 2 ^ (prefixWord ++ tailWord_6814791).sum := by decide
  have hdescent : baseEnd_6814791 < baseStart_6814791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814800 : List Nat := [2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_6814800 : Nat := 118140960795 + 6814800 * 2 ^ 59
def prefixEnd_6814800 : Nat := 4983230072969 + 3 ^ 40 * 6814800 * 2
def baseEnd_6814800 : Nat := 3499267964260042297359311

theorem tailTrace_6814800 : CollatzResearch.WordTrace tailWord_6814800 prefixEnd_6814800 3499267964260042297359311 := by
  unfold tailWord_6814800
  simp only [CollatzResearch.WordTrace]
  refine ⟨124278087855575475012136927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165704117140767300016182569 124278087855575475012136927)
  ·
    refine ⟨186417131783363212518205391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124278087855575475012136927 186417131783363212518205391)
    ·
      refine ⟨279625697675044818777308087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186417131783363212518205391 279625697675044818777308087)
      ·
        refine ⟨419438546512567228165962131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279625697675044818777308087 419438546512567228165962131)
        ·
          refine ⟨629157819768850842248943197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419438546512567228165962131 629157819768850842248943197)
          ·
            refine ⟨235934182413319065843353699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 629157819768850842248943197 235934182413319065843353699)
            ·
              refine ⟨353901273619978598765030549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235934182413319065843353699 353901273619978598765030549)
              ·
                refine ⟨16589122200936496817110807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 353901273619978598765030549 16589122200936496817110807)
                ·
                  refine ⟨24883683301404745225666211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16589122200936496817110807 24883683301404745225666211)
                  ·
                    refine ⟨37325524952107117838499317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24883683301404745225666211 37325524952107117838499317)
                    ·
                      refine ⟨3499267964260042297359311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37325524952107117838499317 3499267964260042297359311)
                      ·
                        rfl

theorem cell23_6814800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_6814800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814800 prefixEnd_6814800 := by exact prefixLift 6814800
  have htrace : WordTrace (prefixWord ++ tailWord_6814800) baseStart_6814800 baseEnd_6814800 := by
    simpa [prefixWord, tailWord_6814800, baseEnd_6814800] using wordTrace_append hprefix tailTrace_6814800
  have hstable : (prefixWord ++ tailWord_6814800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814800).length < 2 ^ (prefixWord ++ tailWord_6814800).sum := by decide
  have hdescent : baseEnd_6814800 < baseStart_6814800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814817 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_6814817 : Nat := 118140960795 + 6814817 * 2 ^ 59
def prefixEnd_6814817 : Nat := 4983230072969 + 3 ^ 40 * 6814817 * 2
def baseEnd_6814817 : Nat := 3499276693431168730846733

theorem tailTrace_6814817 : CollatzResearch.WordTrace tailWord_6814817 prefixEnd_6814817 3499276693431168730846733 := by
  unfold tailWord_6814817
  simp only [CollatzResearch.WordTrace]
  refine ⟨248556795752089361927642705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165704530501392907951761803 248556795752089361927642705)
  ·
    refine ⟨186417596814067021445732029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248556795752089361927642705 186417596814067021445732029)
    ·
      refine ⟨69906598805275133042149511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186417596814067021445732029 69906598805275133042149511)
      ·
        refine ⟨104859898207912699563224267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69906598805275133042149511 104859898207912699563224267)
        ·
          refine ⟨157289847311869049344836401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104859898207912699563224267 157289847311869049344836401)
          ·
            refine ⟨117967385483901787008627301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157289847311869049344836401 117967385483901787008627301)
            ·
              refine ⟨22118884778231585064117619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117967385483901787008627301 22118884778231585064117619)
              ·
                refine ⟨33178327167347377596176429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22118884778231585064117619 33178327167347377596176429)
                ·
                  refine ⟨12441872687755266598566161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33178327167347377596176429 12441872687755266598566161)
                  ·
                    refine ⟨9331404515816449948924621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12441872687755266598566161 9331404515816449948924621)
                    ·
                      refine ⟨3499276693431168730846733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331404515816449948924621 3499276693431168730846733)
                      ·
                        rfl

theorem cell23_6814817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_6814817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814817 prefixEnd_6814817 := by exact prefixLift 6814817
  have htrace : WordTrace (prefixWord ++ tailWord_6814817) baseStart_6814817 baseEnd_6814817 := by
    simpa [prefixWord, tailWord_6814817, baseEnd_6814817] using wordTrace_append hprefix tailTrace_6814817
  have hstable : (prefixWord ++ tailWord_6814817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814817).length < 2 ^ (prefixWord ++ tailWord_6814817).sum := by decide
  have hdescent : baseEnd_6814817 < baseStart_6814817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814818 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6814818 : Nat := 118140960795 + 6814818 * 2 ^ 59
def prefixEnd_6814818 : Nat := 4983230072969 + 3 ^ 40 * 6814818 * 2
def baseEnd_6814818 : Nat := 3499277206911823226934229

theorem tailTrace_6814818 : CollatzResearch.WordTrace tailWord_6814818 prefixEnd_6814818 3499277206911823226934229 := by
  unfold tailWord_6814818
  simp only [CollatzResearch.WordTrace]
  refine ⟨62139208056271434774607277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165704554816723826065619405 62139208056271434774607277)
  ·
    refine ⟨23302203021101788040477729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62139208056271434774607277 23302203021101788040477729)
    ·
      refine ⟨17476652265826341030358297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23302203021101788040477729 17476652265826341030358297)
      ·
        refine ⟨13107489199369755772768723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17476652265826341030358297 13107489199369755772768723)
        ·
          refine ⟨19661233799054633659153085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13107489199369755772768723 19661233799054633659153085)
          ·
            refine ⟨7372962674645487622182407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19661233799054633659153085 7372962674645487622182407)
            ·
              refine ⟨11059444011968231433273611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372962674645487622182407 11059444011968231433273611)
              ·
                refine ⟨16589166017952347149910417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11059444011968231433273611 16589166017952347149910417)
                ·
                  refine ⟨12441874513464260362432813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16589166017952347149910417 12441874513464260362432813)
                  ·
                    refine ⟨4665702942549097635912305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12441874513464260362432813 4665702942549097635912305)
                    ·
                      refine ⟨3499277206911823226934229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665702942549097635912305 3499277206911823226934229)
                      ·
                        rfl

theorem cell23_6814818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6814818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814818 prefixEnd_6814818 := by exact prefixLift 6814818
  have htrace : WordTrace (prefixWord ++ tailWord_6814818) baseStart_6814818 baseEnd_6814818 := by
    simpa [prefixWord, tailWord_6814818, baseEnd_6814818] using wordTrace_append hprefix tailTrace_6814818
  have hstable : (prefixWord ++ tailWord_6814818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814818).length < 2 ^ (prefixWord ++ tailWord_6814818).sum := by decide
  have hdescent : baseEnd_6814818 < baseStart_6814818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814834 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_6814834 : Nat := 118140960795 + 6814834 * 2 ^ 59
def prefixEnd_6814834 : Nat := 4983230072969 + 3 ^ 40 * 6814834 * 2
def baseEnd_6814834 : Nat := 3499285422602295164334155

theorem tailTrace_6814834 : CollatzResearch.WordTrace tailWord_6814834 prefixEnd_6814834 3499285422602295164334155 := by
  unfold tailWord_6814834
  simp only [CollatzResearch.WordTrace]
  refine ⟨62139353948256943457752889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165704943862018515887341037 62139353948256943457752889)
  ·
    refine ⟨46604515461192707593314667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62139353948256943457752889 46604515461192707593314667)
    ·
      refine ⟨69906773191789061389972001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46604515461192707593314667 69906773191789061389972001)
      ·
        refine ⟨52430079893841796042479001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69906773191789061389972001 52430079893841796042479001)
        ·
          refine ⟨39322559920381347031859251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52430079893841796042479001 39322559920381347031859251)
          ·
            refine ⟨58983839880572020547788877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39322559920381347031859251 58983839880572020547788877)
            ·
              refine ⟨22118939955214507705420829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58983839880572020547788877 22118939955214507705420829)
              ·
                refine ⟨8294602483205440389532811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22118939955214507705420829 8294602483205440389532811)
                ·
                  refine ⟨12441903724808160584299217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294602483205440389532811 12441903724808160584299217)
                  ·
                    refine ⟨9331427793606120438224413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12441903724808160584299217 9331427793606120438224413)
                    ·
                      refine ⟨3499285422602295164334155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331427793606120438224413 3499285422602295164334155)
                      ·
                        rfl

theorem cell23_6814834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_6814834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814834 prefixEnd_6814834 := by exact prefixLift 6814834
  have htrace : WordTrace (prefixWord ++ tailWord_6814834) baseStart_6814834 baseEnd_6814834 := by
    simpa [prefixWord, tailWord_6814834, baseEnd_6814834] using wordTrace_append hprefix tailTrace_6814834
  have hstable : (prefixWord ++ tailWord_6814834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814834).length < 2 ^ (prefixWord ++ tailWord_6814834).sum := by decide
  have hdescent : baseEnd_6814834 < baseStart_6814834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814841 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 2, 4]
def baseStart_6814841 : Nat := 118140960795 + 6814841 * 2 ^ 59
def prefixEnd_6814841 : Nat := 4983230072969 + 3 ^ 40 * 6814841 * 2
def baseEnd_6814841 : Nat := 1166429672322292212315541

theorem tailTrace_6814841 : CollatzResearch.WordTrace tailWord_6814841 prefixEnd_6814841 1166429672322292212315541 := by
  unfold tailWord_6814841
  simp only [CollatzResearch.WordTrace]
  refine ⟨248557671104002414026516377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165705114069334942684344251 248557671104002414026516377)
  ·
    refine ⟨186418253328001810519887283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248557671104002414026516377 186418253328001810519887283)
    ·
      refine ⟨279627379992002715779830925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186418253328001810519887283 279627379992002715779830925)
      ·
        refine ⟨104860267497001018417436597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279627379992002715779830925 104860267497001018417436597)
        ·
          refine ⟨9830650077843845476634681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104860267497001018417436597 9830650077843845476634681)
          ·
            refine ⟨7372987558382884107476011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9830650077843845476634681 7372987558382884107476011)
            ·
              refine ⟨11059481337574326161214017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7372987558382884107476011 11059481337574326161214017)
              ·
                refine ⟨8294611003180744620910513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11059481337574326161214017 8294611003180744620910513)
                ·
                  refine ⟨6220958252385558465682885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8294611003180744620910513 6220958252385558465682885)
                  ·
                    refine ⟨1166429672322292212315541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220958252385558465682885 1166429672322292212315541)
                    ·
                      rfl

theorem cell23_6814841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_6814841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814841 prefixEnd_6814841 := by exact prefixLift 6814841
  have htrace : WordTrace (prefixWord ++ tailWord_6814841) baseStart_6814841 baseEnd_6814841 := by
    simpa [prefixWord, tailWord_6814841, baseEnd_6814841] using wordTrace_append hprefix tailTrace_6814841
  have hstable : (prefixWord ++ tailWord_6814841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814841).length < 2 ^ (prefixWord ++ tailWord_6814841).sum := by decide
  have hdescent : baseEnd_6814841 < baseStart_6814841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814860 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6814860 : Nat := 118140960795 + 6814860 * 2 ^ 59
def prefixEnd_6814860 : Nat := 4983230072969 + 3 ^ 40 * 6814860 * 2
def baseEnd_6814860 : Nat := 3499298773099312062609035

theorem tailTrace_6814860 : CollatzResearch.WordTrace tailWord_6814860 prefixEnd_6814860 3499298773099312062609035 := by
  unfold tailWord_6814860
  simp only [CollatzResearch.WordTrace]
  refine ⟨124279182045466790135729017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165705576060622386847638689 124279182045466790135729017)
  ·
    refine ⟨93209386534100092601796763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124279182045466790135729017 93209386534100092601796763)
    ·
      refine ⟨139814079801150138902695145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93209386534100092601796763 139814079801150138902695145)
      ·
        refine ⟨104860559850862604177021359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139814079801150138902695145 104860559850862604177021359)
        ·
          refine ⟨157290839776293906265532039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104860559850862604177021359 157290839776293906265532039)
          ·
            refine ⟨235936259664440859398298059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157290839776293906265532039 235936259664440859398298059)
            ·
              refine ⟨353904389496661289097447089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235936259664440859398298059 353904389496661289097447089)
              ·
                refine ⟨265428292122495966823085317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353904389496661289097447089 265428292122495966823085317)
                ·
                  refine ⟨49767804772967993779328497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265428292122495966823085317 49767804772967993779328497)
                  ·
                    refine ⟨37325853579725995334496373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49767804772967993779328497 37325853579725995334496373)
                    ·
                      refine ⟨3499298773099312062609035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37325853579725995334496373 3499298773099312062609035)
                      ·
                        rfl

theorem cell23_6814860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6814860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814860 prefixEnd_6814860 := by exact prefixLift 6814860
  have htrace : WordTrace (prefixWord ++ tailWord_6814860) baseStart_6814860 baseEnd_6814860 := by
    simpa [prefixWord, tailWord_6814860, baseEnd_6814860] using wordTrace_append hprefix tailTrace_6814860
  have hstable : (prefixWord ++ tailWord_6814860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814860).length < 2 ^ (prefixWord ++ tailWord_6814860).sum := by decide
  have hdescent : baseEnd_6814860 < baseStart_6814860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814882 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_6814882 : Nat := 118140960795 + 6814882 * 2 ^ 59
def prefixEnd_6814882 : Nat := 4983230072969 + 3 ^ 40 * 6814882 * 2
def baseEnd_6814882 : Nat := 3499310069673710976533935

theorem tailTrace_6814882 : CollatzResearch.WordTrace tailWord_6814882 prefixEnd_6814882 3499310069673710976533935 := by
  unfold tailWord_6814882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62139791624213469507189725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165706110997902585352505933 62139791624213469507189725)
  ·
    refine ⟨23302421859080051065196147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62139791624213469507189725 23302421859080051065196147)
    ·
      refine ⟨34953632788620076597794221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23302421859080051065196147 34953632788620076597794221)
      ·
        refine ⟨13107612295732528724172833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34953632788620076597794221 13107612295732528724172833)
        ·
          refine ⟨9830709221799396543129625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13107612295732528724172833 9830709221799396543129625)
          ·
            refine ⟨7373031916349547407347219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9830709221799396543129625 7373031916349547407347219)
            ·
              refine ⟨11059547874524321111020829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7373031916349547407347219 11059547874524321111020829)
              ·
                refine ⟨4147330452946620416632811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11059547874524321111020829 4147330452946620416632811)
                ·
                  refine ⟨6220995679419930624949217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147330452946620416632811 6220995679419930624949217)
                  ·
                    refine ⟨4665746759564947968711913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6220995679419930624949217 4665746759564947968711913)
                    ·
                      refine ⟨3499310069673710976533935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665746759564947968711913 3499310069673710976533935)
                      ·
                        rfl

theorem cell23_6814882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_6814882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814882 prefixEnd_6814882 := by exact prefixLift 6814882
  have htrace : WordTrace (prefixWord ++ tailWord_6814882) baseStart_6814882 baseEnd_6814882 := by
    simpa [prefixWord, tailWord_6814882, baseEnd_6814882] using wordTrace_append hprefix tailTrace_6814882
  have hstable : (prefixWord ++ tailWord_6814882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814882).length < 2 ^ (prefixWord ++ tailWord_6814882).sum := by decide
  have hdescent : baseEnd_6814882 < baseStart_6814882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814925 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6814925 : Nat := 118140960795 + 6814925 * 2 ^ 59
def prefixEnd_6814925 : Nat := 4983230072969 + 3 ^ 40 * 6814925 * 2
def baseEnd_6814925 : Nat := 3499332149341854308296237

theorem tailTrace_6814925 : CollatzResearch.WordTrace tailWord_6814925 prefixEnd_6814925 3499332149341854308296237 := by
  unfold tailWord_6814925
  simp only [CollatzResearch.WordTrace]
  refine ⟨248560734835698096372574229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165707156557132064248382819 248560734835698096372574229)
  ·
    refine ⟨11651284445423348267464417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248560734835698096372574229 11651284445423348267464417)
    ·
      refine ⟨8738463334067511200598313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11651284445423348267464417 8738463334067511200598313)
      ·
        refine ⟨6553847500550633400448735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8738463334067511200598313 6553847500550633400448735)
        ·
          refine ⟨9830771250825950100673103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553847500550633400448735 9830771250825950100673103)
          ·
            refine ⟨14746156876238925151009655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830771250825950100673103 14746156876238925151009655)
            ·
              refine ⟨22119235314358387726514483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14746156876238925151009655 22119235314358387726514483)
              ·
                refine ⟨33178852971537581589771725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22119235314358387726514483 33178852971537581589771725)
                ·
                  refine ⟨12442069864326593096164397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33178852971537581589771725 12442069864326593096164397)
                  ·
                    refine ⟨4665776199122472411061649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12442069864326593096164397 4665776199122472411061649)
                    ·
                      refine ⟨3499332149341854308296237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665776199122472411061649 3499332149341854308296237)
                      ·
                        rfl

theorem cell23_6814925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6814925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814925 prefixEnd_6814925 := by exact prefixLift 6814925
  have htrace : WordTrace (prefixWord ++ tailWord_6814925) baseStart_6814925 baseEnd_6814925 := by
    simpa [prefixWord, tailWord_6814925, baseEnd_6814925] using wordTrace_append hprefix tailTrace_6814925
  have hstable : (prefixWord ++ tailWord_6814925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814925).length < 2 ^ (prefixWord ++ tailWord_6814925).sum := by decide
  have hdescent : baseEnd_6814925 < baseStart_6814925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6814937 : List Nat := [1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_6814937 : Nat := 118140960795 + 6814937 * 2 ^ 59
def prefixEnd_6814937 : Nat := 4983230072969 + 3 ^ 40 * 6814937 * 2
def baseEnd_6814937 : Nat := 3499338311109708261346181

theorem tailTrace_6814937 : CollatzResearch.WordTrace tailWord_6814937 prefixEnd_6814937 3499338311109708261346181 := by
  unfold tailWord_6814937
  simp only [CollatzResearch.WordTrace]
  refine ⟨248561172511654622422011065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165707448341103081614674043 248561172511654622422011065)
  ·
    refine ⟨186420879383740966816508299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248561172511654622422011065 186420879383740966816508299)
    ·
      refine ⟨279631319075611450224762449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186420879383740966816508299 279631319075611450224762449)
      ·
        refine ⟨209723489306708587668571837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279631319075611450224762449 209723489306708587668571837)
        ·
          refine ⟨78646308490015720375714439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209723489306708587668571837 78646308490015720375714439)
          ·
            refine ⟨117969462735023580563571659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78646308490015720375714439 117969462735023580563571659)
            ·
              refine ⟨176954194102535370845357489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117969462735023580563571659 176954194102535370845357489)
              ·
                refine ⟨132715645576901528134018117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176954194102535370845357489 132715645576901528134018117)
                ·
                  refine ⟨24884183545669036525128397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132715645576901528134018117 24884183545669036525128397)
                  ·
                    refine ⟨9331568829625888696923149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24884183545669036525128397 9331568829625888696923149)
                    ·
                      refine ⟨3499338311109708261346181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331568829625888696923149 3499338311109708261346181)
                      ·
                        rfl

theorem cell23_6814937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_6814937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6814937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6814937 prefixEnd_6814937 := by exact prefixLift 6814937
  have htrace : WordTrace (prefixWord ++ tailWord_6814937) baseStart_6814937 baseEnd_6814937 := by
    simpa [prefixWord, tailWord_6814937, baseEnd_6814937] using wordTrace_append hprefix tailTrace_6814937
  have hstable : (prefixWord ++ tailWord_6814937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6814937).length < 2 ^ (prefixWord ++ tailWord_6814937).sum := by decide
  have hdescent : baseEnd_6814937 < baseStart_6814937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6814937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815062 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6815062 : Nat := 118140960795 + 6815062 * 2 ^ 59
def prefixEnd_6815062 : Nat := 4983230072969 + 3 ^ 40 * 6815062 * 2
def baseEnd_6815062 : Nat := 3499402496191520272283107

theorem tailTrace_6815062 : CollatzResearch.WordTrace tailWord_6815062 prefixEnd_6815062 3499402496191520272283107 := by
  unfold tailWord_6815062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535358227262610548144465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165710487757467845846874293 15535358227262610548144465)
  ·
    refine ⟨11651518670446957911108349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15535358227262610548144465 11651518670446957911108349)
    ·
      refine ⟨4369319501417609216665631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11651518670446957911108349 4369319501417609216665631)
      ·
        refine ⟨6553979252126413824998447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369319501417609216665631 6553979252126413824998447)
        ·
          refine ⟨9830968878189620737497671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553979252126413824998447 9830968878189620737497671)
          ·
            refine ⟨14746453317284431106246507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830968878189620737497671 14746453317284431106246507)
            ·
              refine ⟨22119679975926646659369761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14746453317284431106246507 22119679975926646659369761)
              ·
                refine ⟨16589759981944984994527321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22119679975926646659369761 16589759981944984994527321)
                ·
                  refine ⟨12442319986458738745895491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16589759981944984994527321 12442319986458738745895491)
                  ·
                    refine ⟨18663479979688108118843237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12442319986458738745895491 18663479979688108118843237)
                    ·
                      refine ⟨3499402496191520272283107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18663479979688108118843237 3499402496191520272283107)
                      ·
                        rfl

theorem cell23_6815062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6815062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815062 prefixEnd_6815062 := by exact prefixLift 6815062
  have htrace : WordTrace (prefixWord ++ tailWord_6815062) baseStart_6815062 baseEnd_6815062 := by
    simpa [prefixWord, tailWord_6815062, baseEnd_6815062] using wordTrace_append hprefix tailTrace_6815062
  have hstable : (prefixWord ++ tailWord_6815062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815062).length < 2 ^ (prefixWord ++ tailWord_6815062).sum := by decide
  have hdescent : baseEnd_6815062 < baseStart_6815062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815064 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 1, 5]
def baseStart_6815064 : Nat := 118140960795 + 6815064 * 2 ^ 59
def prefixEnd_6815064 : Nat := 4983230072969 + 3 ^ 40 * 6815064 * 2
def baseEnd_6815064 : Nat := 1166467841050943088152699

theorem tailTrace_6815064 : CollatzResearch.WordTrace tailWord_6815064 prefixEnd_6815064 1166467841050943088152699 := by
  unfold tailWord_6815064
  simp only [CollatzResearch.WordTrace]
  refine ⟨124282902291097261555942123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165710536388129682074589497 124282902291097261555942123)
  ·
    refine ⟨186424353436645892333913185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124282902291097261555942123 186424353436645892333913185)
    ·
      refine ⟨139818265077484419250434889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186424353436645892333913185 139818265077484419250434889)
      ·
        refine ⟨104863698808113314437826167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139818265077484419250434889 104863698808113314437826167)
        ·
          refine ⟨157295548212169971656739251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104863698808113314437826167 157295548212169971656739251)
          ·
            refine ⟨235943322318254957485108877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157295548212169971656739251 235943322318254957485108877)
            ·
              refine ⟨88478745869345609056915829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235943322318254957485108877 88478745869345609056915829)
              ·
                refine ⟨8294882425251150849085859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88478745869345609056915829 8294882425251150849085859)
                ·
                  refine ⟨12442323637876726273628789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294882425251150849085859 12442323637876726273628789)
                  ·
                    refine ⟨1166467841050943088152699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12442323637876726273628789 1166467841050943088152699)
                    ·
                      rfl

theorem cell23_6815064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_6815064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815064 prefixEnd_6815064 := by exact prefixLift 6815064
  have htrace : WordTrace (prefixWord ++ tailWord_6815064) baseStart_6815064 baseEnd_6815064 := by
    simpa [prefixWord, tailWord_6815064, baseEnd_6815064] using wordTrace_append hprefix tailTrace_6815064
  have hstable : (prefixWord ++ tailWord_6815064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815064).length < 2 ^ (prefixWord ++ tailWord_6815064).sum := by decide
  have hdescent : baseEnd_6815064 < baseStart_6815064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815105 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_6815105 : Nat := 118140960795 + 6815105 * 2 ^ 59
def prefixEnd_6815105 : Nat := 4983230072969 + 3 ^ 40 * 6815105 * 2
def baseEnd_6815105 : Nat := 3499424575859663604045409

theorem tailTrace_6815105 : CollatzResearch.WordTrace tailWord_6815105 prefixEnd_6815105 3499424575859663604045409 := by
  unfold tailWord_6815105
  simp only [CollatzResearch.WordTrace]
  refine ⟨248567299975045987114126769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165711533316697324742751179 248567299975045987114126769)
  ·
    refine ⟨186425474981284490335595077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248567299975045987114126769 186425474981284490335595077)
    ·
      refine ⟨34954776558990841937924077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186425474981284490335595077 34954776558990841937924077)
      ·
        refine ⟨13108041209621565726721529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34954776558990841937924077 13108041209621565726721529)
        ·
          refine ⟨9831030907216174295041147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108041209621565726721529 9831030907216174295041147)
          ·
            refine ⟨14746546360824261442561721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831030907216174295041147 14746546360824261442561721)
            ·
              refine ⟨11059909770618196081921291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14746546360824261442561721 11059909770618196081921291)
              ·
                refine ⟨16589864655927294122881937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11059909770618196081921291 16589864655927294122881937)
                ·
                  refine ⟨12442398491945470592161453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16589864655927294122881937 12442398491945470592161453)
                  ·
                    refine ⟨4665899434479551472060545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12442398491945470592161453 4665899434479551472060545)
                    ·
                      refine ⟨3499424575859663604045409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665899434479551472060545 3499424575859663604045409)
                      ·
                        rfl

theorem cell23_6815105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_6815105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815105 prefixEnd_6815105 := by exact prefixLift 6815105
  have htrace : WordTrace (prefixWord ++ tailWord_6815105) baseStart_6815105 baseEnd_6815105 := by
    simpa [prefixWord, tailWord_6815105, baseEnd_6815105] using wordTrace_append hprefix tailTrace_6815105
  have hstable : (prefixWord ++ tailWord_6815105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815105).length < 2 ^ (prefixWord ++ tailWord_6815105).sum := by decide
  have hdescent : baseEnd_6815105 < baseStart_6815105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815124 : List Nat := [2, 4, 2, 1, 2, 12]
def baseStart_6815124 : Nat := 118140960795 + 6815124 * 2 ^ 59
def prefixEnd_6815124 : Nat := 4983230072969 + 3 ^ 40 * 6815124 * 2
def baseEnd_6815124 : Nat := 14400964329185592714847

theorem tailTrace_6815124 : CollatzResearch.WordTrace tailWord_6815124 prefixEnd_6815124 14400964329185592714847 := by
  unfold tailWord_6815124
  simp only [CollatzResearch.WordTrace]
  refine ⟨124283996480988576679534213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165711995307984768906045617 124283996480988576679534213)
  ·
    refine ⟨23303249340185358127412665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124283996480988576679534213 23303249340185358127412665)
    ·
      refine ⟨17477437005139018595559499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23303249340185358127412665 17477437005139018595559499)
      ·
        refine ⟨26216155507708527893339249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17477437005139018595559499 26216155507708527893339249)
        ·
          refine ⟨19662116630781395920004437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26216155507708527893339249 19662116630781395920004437)
          ·
            refine ⟨14400964329185592714847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 19662116630781395920004437 14400964329185592714847)
            ·
              rfl

theorem cell23_6815124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 12].length) (baseStart_6815124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815124 prefixEnd_6815124 := by exact prefixLift 6815124
  have htrace : WordTrace (prefixWord ++ tailWord_6815124) baseStart_6815124 baseEnd_6815124 := by
    simpa [prefixWord, tailWord_6815124, baseEnd_6815124] using wordTrace_append hprefix tailTrace_6815124
  have hstable : (prefixWord ++ tailWord_6815124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815124).length < 2 ^ (prefixWord ++ tailWord_6815124).sum := by decide
  have hdescent : baseEnd_6815124 < baseStart_6815124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815172 : List Nat := [2, 3, 3, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6815172 : Nat := 118140960795 + 6815172 * 2 ^ 59
def prefixEnd_6815172 : Nat := 4983230072969 + 3 ^ 40 * 6815172 * 2
def baseEnd_6815172 : Nat := 3499458979063514841907601

theorem tailTrace_6815172 : CollatzResearch.WordTrace tailWord_6815172 prefixEnd_6815172 3499458979063514841907601 := by
  unfold tailWord_6815172
  simp only [CollatzResearch.WordTrace]
  refine ⟨124284871832901628778407885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165713162443868838371210513 124284871832901628778407885)
  ·
    refine ⟨46606826937338110791902957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124284871832901628778407885 46606826937338110791902957)
    ·
      refine ⟨17477560101501791546963609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46606826937338110791902957 17477560101501791546963609)
      ·
        refine ⟨13108170076126343660222707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17477560101501791546963609 13108170076126343660222707)
        ·
          refine ⟨19662255114189515490334061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13108170076126343660222707 19662255114189515490334061)
          ·
            refine ⟨7373345667821068308875273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19662255114189515490334061 7373345667821068308875273)
            ·
              refine ⟨5530009250865801231656455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7373345667821068308875273 5530009250865801231656455)
              ·
                refine ⟨8295013876298701847484683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530009250865801231656455 8295013876298701847484683)
                ·
                  refine ⟨12442520814448052771227025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295013876298701847484683 12442520814448052771227025)
                  ·
                    refine ⟨9331890610836039578420269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12442520814448052771227025 9331890610836039578420269)
                    ·
                      refine ⟨3499458979063514841907601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9331890610836039578420269 3499458979063514841907601)
                      ·
                        rfl

theorem cell23_6815172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6815172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815172 prefixEnd_6815172 := by exact prefixLift 6815172
  have htrace : WordTrace (prefixWord ++ tailWord_6815172) baseStart_6815172 baseEnd_6815172 := by
    simpa [prefixWord, tailWord_6815172, baseEnd_6815172] using wordTrace_append hprefix tailTrace_6815172
  have hstable : (prefixWord ++ tailWord_6815172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815172).length < 2 ^ (prefixWord ++ tailWord_6815172).sum := by decide
  have hdescent : baseEnd_6815172 < baseStart_6815172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815191 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 3, 4, 2]
def baseStart_6815191 : Nat := 118140960795 + 6815191 * 2 ^ 59
def prefixEnd_6815191 : Nat := 4983230072969 + 3 ^ 40 * 6815191 * 2
def baseEnd_6815191 : Nat := 3499468735195950267570013

theorem tailTrace_6815191 : CollatzResearch.WordTrace tailWord_6815191 prefixEnd_6815191 3499468735195950267570013 := by
  unfold tailWord_6815191
  simp only [CollatzResearch.WordTrace]
  refine ⟨248570436652734423801757427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165713624435156282534504951 248570436652734423801757427)
  ·
    refine ⟨372855654979101635702636141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248570436652734423801757427 372855654979101635702636141)
    ·
      refine ⟨139820870617163113388488553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372855654979101635702636141 139820870617163113388488553)
      ·
        refine ⟨104865652962872335041366415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139820870617163113388488553 104865652962872335041366415)
        ·
          refine ⟨157298479444308502562049623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104865652962872335041366415 157298479444308502562049623)
          ·
            refine ⟨235947719166462753843074435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157298479444308502562049623 235947719166462753843074435)
            ·
              refine ⟨353921578749694130764611653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235947719166462753843074435 353921578749694130764611653)
              ·
                refine ⟨66360296015567649518364685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353921578749694130764611653 66360296015567649518364685)
                ·
                  refine ⟨24885111005837868569386757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66360296015567649518364685 24885111005837868569386757)
                  ·
                    refine ⟨4665958313594600356760017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24885111005837868569386757 4665958313594600356760017)
                    ·
                      refine ⟨3499468735195950267570013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4665958313594600356760017 3499468735195950267570013)
                      ·
                        rfl

theorem cell23_6815191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_6815191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815191 prefixEnd_6815191 := by exact prefixLift 6815191
  have htrace : WordTrace (prefixWord ++ tailWord_6815191) baseStart_6815191 baseEnd_6815191 := by
    simpa [prefixWord, tailWord_6815191, baseEnd_6815191] using wordTrace_append hprefix tailTrace_6815191
  have hstable : (prefixWord ++ tailWord_6815191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815191).length < 2 ^ (prefixWord ++ tailWord_6815191).sum := by decide
  have hdescent : baseEnd_6815191 < baseStart_6815191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815231 : List Nat := [1, 1, 2, 2, 1, 2, 2, 7, 5]
def baseStart_6815231 : Nat := 118140960795 + 6815231 * 2 ^ 59
def prefixEnd_6815231 : Nat := 4983230072969 + 3 ^ 40 * 6815231 * 2
def baseEnd_6815231 : Nat := 388832141602458901229981

theorem tailTrace_6815231 : CollatzResearch.WordTrace tailWord_6815231 prefixEnd_6815231 388832141602458901229981 := by
  unfold tailWord_6815231
  simp only [CollatzResearch.WordTrace]
  refine ⟨248571895572589510633213547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165714597048393007088809031 248571895572589510633213547)
  ·
    refine ⟨372857843358884265949820321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248571895572589510633213547 372857843358884265949820321)
    ·
      refine ⟨279643382519163199462365241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372857843358884265949820321 279643382519163199462365241)
      ·
        refine ⟨209732536889372399596773931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279643382519163199462365241 209732536889372399596773931)
        ·
          refine ⟨314598805334058599395160897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209732536889372399596773931 314598805334058599395160897)
          ·
            refine ⟨235949104000543949546370673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314598805334058599395160897 235949104000543949546370673)
            ·
              refine ⟨176961828000407962159778005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235949104000543949546370673 176961828000407962159778005)
              ·
                refine ⟨4147542843759561613119797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 176961828000407962159778005 4147542843759561613119797)
                ·
                  refine ⟨388832141602458901229981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4147542843759561613119797 388832141602458901229981)
                  ·
                    rfl

theorem cell23_6815231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 5].length) (baseStart_6815231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815231 prefixEnd_6815231 := by exact prefixLift 6815231
  have htrace : WordTrace (prefixWord ++ tailWord_6815231) baseStart_6815231 baseEnd_6815231 := by
    simpa [prefixWord, tailWord_6815231, baseEnd_6815231] using wordTrace_append hprefix tailTrace_6815231
  have hstable : (prefixWord ++ tailWord_6815231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815231).length < 2 ^ (prefixWord ++ tailWord_6815231).sum := by decide
  have hdescent : baseEnd_6815231 < baseStart_6815231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815261 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6815261 : Nat := 118140960795 + 6815261 * 2 ^ 59
def prefixEnd_6815261 : Nat := 4983230072969 + 3 ^ 40 * 6815261 * 2
def baseEnd_6815261 : Nat := 1166501559613921664564897

theorem tailTrace_6815261 : CollatzResearch.WordTrace tailWord_6815261 prefixEnd_6815261 1166501559613921664564897 := by
  unfold tailWord_6815261
  simp only [CollatzResearch.WordTrace]
  refine ⟨248572989762480825756805637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165715326508320550504537091 248572989762480825756805637)
  ·
    refine ⟨46607435580465154829401057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248572989762480825756805637 46607435580465154829401057)
    ·
      refine ⟨34955576685348866122050793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46607435580465154829401057 34955576685348866122050793)
      ·
        refine ⟨26216682514011649591538095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34955576685348866122050793 26216682514011649591538095)
        ·
          refine ⟨39325023771017474387307143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26216682514011649591538095 39325023771017474387307143)
          ·
            refine ⟨58987535656526211580960715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39325023771017474387307143 58987535656526211580960715)
            ·
              refine ⟨88481303484789317371441073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58987535656526211580960715 88481303484789317371441073)
              ·
                refine ⟨66360977613591988028580805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88481303484789317371441073 66360977613591988028580805)
                ·
                  refine ⟨12442683302548497755358901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66360977613591988028580805 12442683302548497755358901)
                  ·
                    refine ⟨1166501559613921664564897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12442683302548497755358901 1166501559613921664564897)
                    ·
                      rfl

theorem cell23_6815261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6815261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815261 prefixEnd_6815261 := by exact prefixLift 6815261
  have htrace : WordTrace (prefixWord ++ tailWord_6815261) baseStart_6815261 baseEnd_6815261 := by
    simpa [prefixWord, tailWord_6815261, baseEnd_6815261] using wordTrace_append hprefix tailTrace_6815261
  have hstable : (prefixWord ++ tailWord_6815261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815261).length < 2 ^ (prefixWord ++ tailWord_6815261).sum := by decide
  have hdescent : baseEnd_6815261 < baseStart_6815261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815278 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6815278 : Nat := 118140960795 + 6815278 * 2 ^ 59
def prefixEnd_6815278 : Nat := 4983230072969 + 3 ^ 40 * 6815278 * 2
def baseEnd_6815278 : Nat := 1166504469337630475727371

theorem tailTrace_6815278 : CollatzResearch.WordTrace tailWord_6815278 prefixEnd_6815278 1166504469337630475727371 := by
  unfold tailWord_6815278
  simp only [CollatzResearch.WordTrace]
  refine ⟨31071701225427404707521811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165715739868946158440116325 31071701225427404707521811)
  ·
    refine ⟨46607551838141107061282717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31071701225427404707521811 46607551838141107061282717)
    ·
      refine ⟨17477831939302915147981019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46607551838141107061282717 17477831939302915147981019)
      ·
        refine ⟨26216747908954372721971529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17477831939302915147981019 26216747908954372721971529)
        ·
          refine ⟨19662560931715779541478647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26216747908954372721971529 19662560931715779541478647)
          ·
            refine ⟨29493841397573669312217971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19662560931715779541478647 29493841397573669312217971)
            ·
              refine ⟨44240762096360503968326957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29493841397573669312217971 44240762096360503968326957)
              ·
                refine ⟨16590285786135188988122609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44240762096360503968326957 16590285786135188988122609)
                ·
                  refine ⟨12442714339601391741091957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16590285786135188988122609 12442714339601391741091957)
                  ·
                    refine ⟨1166504469337630475727371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12442714339601391741091957 1166504469337630475727371)
                    ·
                      rfl

theorem cell23_6815278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6815278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815278 prefixEnd_6815278 := by exact prefixLift 6815278
  have htrace : WordTrace (prefixWord ++ tailWord_6815278) baseStart_6815278 baseEnd_6815278 := by
    simpa [prefixWord, tailWord_6815278, baseEnd_6815278] using wordTrace_append hprefix tailTrace_6815278
  have hstable : (prefixWord ++ tailWord_6815278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815278).length < 2 ^ (prefixWord ++ tailWord_6815278).sum := by decide
  have hdescent : baseEnd_6815278 < baseStart_6815278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815365 : List Nat := [1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_6815365 : Nat := 118140960795 + 6815365 * 2 ^ 59
def prefixEnd_6815365 : Nat := 4983230072969 + 3 ^ 40 * 6815365 * 2
def baseEnd_6815365 : Nat := 3499558080829832586794213

theorem tailTrace_6815365 : CollatzResearch.WordTrace tailWord_6815365 prefixEnd_6815365 3499558080829832586794213 := by
  unfold tailWord_6815365
  simp only [CollatzResearch.WordTrace]
  refine ⟨248576782954104051518591549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165717855302736034345727699 248576782954104051518591549)
  ·
    refine ⟨93216293607789019319471831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248576782954104051518591549 93216293607789019319471831)
    ·
      refine ⟨139824440411683528979207747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93216293607789019319471831 139824440411683528979207747)
      ·
        refine ⟨209736660617525293468811621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139824440411683528979207747 209736660617525293468811621)
        ·
          refine ⟨39325623865785992525402179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209736660617525293468811621 39325623865785992525402179)
          ·
            refine ⟨58988435798678988788103269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39325623865785992525402179 58988435798678988788103269)
            ·
              refine ⟨11060331712252310397769363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58988435798678988788103269 11060331712252310397769363)
              ·
                refine ⟨16590497568378465596654045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11060331712252310397769363 16590497568378465596654045)
                ·
                  refine ⟨6221436588141924598745267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16590497568378465596654045 6221436588141924598745267)
                  ·
                    refine ⟨9332154882212886898117901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6221436588141924598745267 9332154882212886898117901)
                    ·
                      refine ⟨3499558080829832586794213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9332154882212886898117901 3499558080829832586794213)
                      ·
                        rfl

theorem cell23_6815365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_6815365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815365 prefixEnd_6815365 := by exact prefixLift 6815365
  have htrace : WordTrace (prefixWord ++ tailWord_6815365) baseStart_6815365 baseEnd_6815365 := by
    simpa [prefixWord, tailWord_6815365, baseEnd_6815365] using wordTrace_append hprefix tailTrace_6815365
  have hstable : (prefixWord ++ tailWord_6815365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815365).length < 2 ^ (prefixWord ++ tailWord_6815365).sum := by decide
  have hdescent : baseEnd_6815365 < baseStart_6815365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815405 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_6815405 : Nat := 118140960795 + 6815405 * 2 ^ 59
def prefixEnd_6815405 : Nat := 4983230072969 + 3 ^ 40 * 6815405 * 2
def baseEnd_6815405 : Nat := 3499578620056012430294029

theorem tailTrace_6815405 : CollatzResearch.WordTrace tailWord_6815405 prefixEnd_6815405 3499578620056012430294029 := by
  unfold tailWord_6815405
  simp only [CollatzResearch.WordTrace]
  refine ⟨248578241873959138350047669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165718827915972758900031779 248578241873959138350047669)
  ·
    refine ⟨23304210175683669220316969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248578241873959138350047669 23304210175683669220316969)
    ·
      refine ⟨17478157631762751915237727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23304210175683669220316969 17478157631762751915237727)
      ·
        refine ⟨26217236447644127872856591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478157631762751915237727 26217236447644127872856591)
        ·
          refine ⟨39325854671466191809284887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26217236447644127872856591 39325854671466191809284887)
          ·
            refine ⟨58988782007199287713927331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39325854671466191809284887 58988782007199287713927331)
            ·
              refine ⟨88483173010798931570890997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58988782007199287713927331 88483173010798931570890997)
              ·
                refine ⟨8295297469762399834771031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88483173010798931570890997 8295297469762399834771031)
                ·
                  refine ⟨12442946204643599752156547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295297469762399834771031 12442946204643599752156547)
                  ·
                    refine ⟨18664419306965399628234821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12442946204643599752156547 18664419306965399628234821)
                    ·
                      refine ⟨3499578620056012430294029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18664419306965399628234821 3499578620056012430294029)
                      ·
                        rfl

theorem cell23_6815405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_6815405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815405 prefixEnd_6815405 := by exact prefixLift 6815405
  have htrace : WordTrace (prefixWord ++ tailWord_6815405) baseStart_6815405 baseEnd_6815405 := by
    simpa [prefixWord, tailWord_6815405, baseEnd_6815405] using wordTrace_append hprefix tailTrace_6815405
  have hstable : (prefixWord ++ tailWord_6815405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815405).length < 2 ^ (prefixWord ++ tailWord_6815405).sum := by decide
  have hdescent : baseEnd_6815405 < baseStart_6815405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815428 : List Nat := [2, 3, 3, 1, 1, 1, 4, 8]
def baseStart_6815428 : Nat := 118140960795 + 6815428 * 2 ^ 59
def prefixEnd_6815428 : Nat := 4983230072969 + 3 ^ 40 * 6815428 * 2
def baseEnd_6815428 : Nat := 129614460374483920011349

theorem tailTrace_6815428 : CollatzResearch.WordTrace tailWord_6815428 prefixEnd_6815428 129614460374483920011349 := by
  unfold tailWord_6815428
  simp only [CollatzResearch.WordTrace]
  refine ⟨124289540376437906639067469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165719387168583875518756625 124289540376437906639067469)
  ·
    refine ⟨46608577641164214989650301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124289540376437906639067469 46608577641164214989650301)
    ·
      refine ⟨17478216615436580621118863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46608577641164214989650301 17478216615436580621118863)
      ·
        refine ⟨26217324923154870931678295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478216615436580621118863 26217324923154870931678295)
        ·
          refine ⟨39325987384732306397517443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26217324923154870931678295 39325987384732306397517443)
          ·
            refine ⟨58988981077098459596276165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39325987384732306397517443 58988981077098459596276165)
            ·
              refine ⟨11060433951955961174301781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58988981077098459596276165 11060433951955961174301781)
              ·
                refine ⟨129614460374483920011349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11060433951955961174301781 129614460374483920011349)
                ·
                  rfl

theorem cell23_6815428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 8].length) (baseStart_6815428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815428 prefixEnd_6815428 := by exact prefixLift 6815428
  have htrace : WordTrace (prefixWord ++ tailWord_6815428) baseStart_6815428 baseEnd_6815428 := by
    simpa [prefixWord, tailWord_6815428, baseEnd_6815428] using wordTrace_append hprefix tailTrace_6815428
  have hstable : (prefixWord ++ tailWord_6815428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815428).length < 2 ^ (prefixWord ++ tailWord_6815428).sum := by decide
  have hdescent : baseEnd_6815428 < baseStart_6815428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815431 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_6815431 : Nat := 118140960795 + 6815431 * 2 ^ 59
def prefixEnd_6815431 : Nat := 4983230072969 + 3 ^ 40 * 6815431 * 2
def baseEnd_6815431 : Nat := 3499591970553029328568909

theorem tailTrace_6815431 : CollatzResearch.WordTrace tailWord_6815431 prefixEnd_6815431 3499591970553029328568909 := by
  unfold tailWord_6815431
  simp only [CollatzResearch.WordTrace]
  refine ⟨248579190171864944790494147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165719460114576629860329431 248579190171864944790494147)
  ·
    refine ⟨372868785257797417185741221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248579190171864944790494147 372868785257797417185741221)
    ·
      refine ⟨69912897235837015722326479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372868785257797417185741221 69912897235837015722326479)
      ·
        refine ⟨104869345853755523583489719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69912897235837015722326479 104869345853755523583489719)
        ·
          refine ⟨157304018780633285375234579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104869345853755523583489719 157304018780633285375234579)
          ·
            refine ⟨235956028170949928062851869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157304018780633285375234579 235956028170949928062851869)
            ·
              refine ⟨88483510564106223023569451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235956028170949928062851869 88483510564106223023569451)
              ·
                refine ⟨132725265846159334535354177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88483510564106223023569451 132725265846159334535354177)
                ·
                  refine ⟨99543949384619500901515633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132725265846159334535354177 99543949384619500901515633)
                  ·
                    refine ⟨74657962038464625676136725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99543949384619500901515633 74657962038464625676136725)
                    ·
                      refine ⟨3499591970553029328568909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74657962038464625676136725 3499591970553029328568909)
                      ·
                        rfl

theorem cell23_6815431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_6815431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815431 prefixEnd_6815431 := by exact prefixLift 6815431
  have htrace : WordTrace (prefixWord ++ tailWord_6815431) baseStart_6815431 baseEnd_6815431 := by
    simpa [prefixWord, tailWord_6815431, baseEnd_6815431] using wordTrace_append hprefix tailTrace_6815431
  have hstable : (prefixWord ++ tailWord_6815431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815431).length < 2 ^ (prefixWord ++ tailWord_6815431).sum := by decide
  have hdescent : baseEnd_6815431 < baseStart_6815431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815442 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_6815442 : Nat := 118140960795 + 6815442 * 2 ^ 59
def prefixEnd_6815442 : Nat := 4983230072969 + 3 ^ 40 * 6815442 * 2
def baseEnd_6815442 : Nat := 3499597618840228785531359

theorem tailTrace_6815442 : CollatzResearch.WordTrace tailWord_6815442 prefixEnd_6815442 3499597618840228785531359 := by
  unfold tailWord_6815442
  simp only [CollatzResearch.WordTrace]
  refine ⟨62144897843706273417286145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165719727583216729112763053 62144897843706273417286145)
  ·
    refine ⟨46608673382779705062964609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62144897843706273417286145 46608673382779705062964609)
    ·
      refine ⟨34956505037084778797223457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46608673382779705062964609 34956505037084778797223457)
      ·
        refine ⟨26217378777813584097917593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34956505037084778797223457 26217378777813584097917593)
        ·
          refine ⟨19663034083360188073438195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26217378777813584097917593 19663034083360188073438195)
          ·
            refine ⟨29494551125040282110157293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19663034083360188073438195 29494551125040282110157293)
            ·
              refine ⟨11060456671890105791308985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29494551125040282110157293 11060456671890105791308985)
              ·
                refine ⟨8295342503917579343481739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11060456671890105791308985 8295342503917579343481739)
                ·
                  refine ⟨12443013755876369015222609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295342503917579343481739 12443013755876369015222609)
                  ·
                    refine ⟨9332260316907276761416957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12443013755876369015222609 9332260316907276761416957)
                    ·
                      refine ⟨3499597618840228785531359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9332260316907276761416957 3499597618840228785531359)
                      ·
                        rfl

theorem cell23_6815442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_6815442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815442 prefixEnd_6815442 := by exact prefixLift 6815442
  have htrace : WordTrace (prefixWord ++ tailWord_6815442) baseStart_6815442 baseEnd_6815442 := by
    simpa [prefixWord, tailWord_6815442, baseEnd_6815442] using wordTrace_append hprefix tailTrace_6815442
  have hstable : (prefixWord ++ tailWord_6815442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815442).length < 2 ^ (prefixWord ++ tailWord_6815442).sum := by decide
  have hdescent : baseEnd_6815442 < baseStart_6815442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815452 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6815452 : Nat := 118140960795 + 6815452 * 2 ^ 59
def prefixEnd_6815452 : Nat := 4983230072969 + 3 ^ 40 * 6815452 * 2
def baseEnd_6815452 : Nat := 3499602753646773746406313

theorem tailTrace_6815452 : CollatzResearch.WordTrace tailWord_6815452 prefixEnd_6815452 3499602753646773746406313 := by
  unfold tailWord_6815452
  simp only [CollatzResearch.WordTrace]
  refine ⟨124289978052394432688504305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165719970736525910251339073 124289978052394432688504305)
  ·
    refine ⟨93217483539295824516378229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124289978052394432688504305 93217483539295824516378229)
    ·
      refine ⟨8739139081808983548410459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93217483539295824516378229 8739139081808983548410459)
      ·
        refine ⟨13108708622713475322615689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8739139081808983548410459 13108708622713475322615689)
        ·
          refine ⟨9831531467035106491961767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108708622713475322615689 9831531467035106491961767)
          ·
            refine ⟨14747297200552659737942651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831531467035106491961767 14747297200552659737942651)
            ·
              refine ⟨22120945800828989606913977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14747297200552659737942651 22120945800828989606913977)
              ·
                refine ⟨16590709350621742205185483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22120945800828989606913977 16590709350621742205185483)
                ·
                  refine ⟨24886064025932613307778225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16590709350621742205185483 24886064025932613307778225)
                  ·
                    refine ⟨18664548019449459980833669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24886064025932613307778225 18664548019449459980833669)
                    ·
                      refine ⟨3499602753646773746406313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18664548019449459980833669 3499602753646773746406313)
                      ·
                        rfl

theorem cell23_6815452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6815452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815452 prefixEnd_6815452 := by exact prefixLift 6815452
  have htrace : WordTrace (prefixWord ++ tailWord_6815452) baseStart_6815452 baseEnd_6815452 := by
    simpa [prefixWord, tailWord_6815452, baseEnd_6815452] using wordTrace_append hprefix tailTrace_6815452
  have hstable : (prefixWord ++ tailWord_6815452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815452).length < 2 ^ (prefixWord ++ tailWord_6815452).sum := by decide
  have hdescent : baseEnd_6815452 < baseStart_6815452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815459 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6815459 : Nat := 118140960795 + 6815459 * 2 ^ 59
def prefixEnd_6815459 : Nat := 4983230072969 + 3 ^ 40 * 6815459 * 2
def baseEnd_6815459 : Nat := 3499606348011355219018781

theorem tailTrace_6815459 : CollatzResearch.WordTrace tailWord_6815459 prefixEnd_6815459 3499606348011355219018781 := by
  unfold tailWord_6815459
  simp only [CollatzResearch.WordTrace]
  refine ⟨248580211415763505572513431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165720140943842337048342287 248580211415763505572513431)
  ·
    refine ⟨372870317123645258358770147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248580211415763505572513431 372870317123645258358770147)
    ·
      refine ⟨559305475685467887538155221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372870317123645258358770147 559305475685467887538155221)
      ·
        refine ⟨13108722086378153614175513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 559305475685467887538155221 13108722086378153614175513)
        ·
          refine ⟨9831541564783615210631635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108722086378153614175513 9831541564783615210631635)
          ·
            refine ⟨14747312347175422815947453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831541564783615210631635 14747312347175422815947453)
            ·
              refine ⟨5530242130190783555980295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14747312347175422815947453 5530242130190783555980295)
              ·
                refine ⟨8295363195286175333970443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530242130190783555980295 8295363195286175333970443)
                ·
                  refine ⟨12443044792929263000955665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295363195286175333970443 12443044792929263000955665)
                  ·
                    refine ⟨9332283594696947250716749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12443044792929263000955665 9332283594696947250716749)
                    ·
                      refine ⟨3499606348011355219018781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9332283594696947250716749 3499606348011355219018781)
                      ·
                        rfl

theorem cell23_6815459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6815459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815459 prefixEnd_6815459 := by exact prefixLift 6815459
  have htrace : WordTrace (prefixWord ++ tailWord_6815459) baseStart_6815459 baseEnd_6815459 := by
    simpa [prefixWord, tailWord_6815459, baseEnd_6815459] using wordTrace_append hprefix tailTrace_6815459
  have hstable : (prefixWord ++ tailWord_6815459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815459).length < 2 ^ (prefixWord ++ tailWord_6815459).sum := by decide
  have hdescent : baseEnd_6815459 < baseStart_6815459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815542 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6815542 : Nat := 118140960795 + 6815542 * 2 ^ 59
def prefixEnd_6815542 : Nat := 4983230072969 + 3 ^ 40 * 6815542 * 2
def baseEnd_6815542 : Nat := 3499648966905678394280899

theorem tailTrace_6815542 : CollatzResearch.WordTrace tailWord_6815542 prefixEnd_6815542 3499648966905678394280899 := by
  unfold tailWord_6815542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15536452417153925671736555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165722159116308540498523253 15536452417153925671736555)
  ·
    refine ⟨23304678625730888507604833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15536452417153925671736555 23304678625730888507604833)
    ·
      refine ⟨17478508969298166380703625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23304678625730888507604833 17478508969298166380703625)
      ·
        refine ⟨13108881726973624785527719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17478508969298166380703625 13108881726973624785527719)
        ·
          refine ⟨19663322590460437178291579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13108881726973624785527719 19663322590460437178291579)
          ·
            refine ⟨29494983885690655767437369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19663322590460437178291579 29494983885690655767437369)
            ·
              refine ⟨22121237914267991825578027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29494983885690655767437369 22121237914267991825578027)
              ·
                refine ⟨33181856871401987738367041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22121237914267991825578027 33181856871401987738367041)
                ·
                  refine ⟨24886392653551490803775281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33181856871401987738367041 24886392653551490803775281)
                  ·
                    refine ⟨18664794490163618102831461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24886392653551490803775281 18664794490163618102831461)
                    ·
                      refine ⟨3499648966905678394280899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18664794490163618102831461 3499648966905678394280899)
                      ·
                        rfl

theorem cell23_6815542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6815542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815542 prefixEnd_6815542 := by exact prefixLift 6815542
  have htrace : WordTrace (prefixWord ++ tailWord_6815542) baseStart_6815542 baseEnd_6815542 := by
    simpa [prefixWord, tailWord_6815542, baseEnd_6815542] using wordTrace_append hprefix tailTrace_6815542
  have hstable : (prefixWord ++ tailWord_6815542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815542).length < 2 ^ (prefixWord ++ tailWord_6815542).sum := by decide
  have hdescent : baseEnd_6815542 < baseStart_6815542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815546 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2]
def baseStart_6815546 : Nat := 118140960795 + 6815546 * 2 ^ 59
def prefixEnd_6815546 : Nat := 4983230072969 + 3 ^ 40 * 6815546 * 2
def baseEnd_6815546 : Nat := 3499651020828296378630881

theorem tailTrace_6815546 : CollatzResearch.WordTrace tailWord_6815546 prefixEnd_6815546 3499651020828296378630881 := by
  unfold tailWord_6815546
  simp only [CollatzResearch.WordTrace]
  refine ⟨62145846141612079857732623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165722256377632212953953661 62145846141612079857732623)
  ·
    refine ⟨93218769212418119786598935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62145846141612079857732623 93218769212418119786598935)
    ·
      refine ⟨139828153818627179679898403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93218769212418119786598935 139828153818627179679898403)
      ·
        refine ⟨209742230727940769519847605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139828153818627179679898403 209742230727940769519847605)
        ·
          refine ⟨19663334130744447142485713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209742230727940769519847605 19663334130744447142485713)
          ·
            refine ⟨14747500598058335356864285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19663334130744447142485713 14747500598058335356864285)
            ·
              refine ⟨5530312724271875758824107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14747500598058335356864285 5530312724271875758824107)
              ·
                refine ⟨8295469086407813638236161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530312724271875758824107 8295469086407813638236161)
                ·
                  refine ⟨6221601814805860228677121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8295469086407813638236161 6221601814805860228677121)
                  ·
                    refine ⟨4666201361104395171507841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6221601814805860228677121 4666201361104395171507841)
                    ·
                      refine ⟨3499651020828296378630881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666201361104395171507841 3499651020828296378630881)
                      ·
                        rfl

theorem cell23_6815546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_6815546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815546 prefixEnd_6815546 := by exact prefixLift 6815546
  have htrace : WordTrace (prefixWord ++ tailWord_6815546) baseStart_6815546 baseEnd_6815546 := by
    simpa [prefixWord, tailWord_6815546, baseEnd_6815546] using wordTrace_append hprefix tailTrace_6815546
  have hstable : (prefixWord ++ tailWord_6815546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815546).length < 2 ^ (prefixWord ++ tailWord_6815546).sum := by decide
  have hdescent : baseEnd_6815546 < baseStart_6815546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815548 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 1, 7]
def baseStart_6815548 : Nat := 118140960795 + 6815548 * 2 ^ 59
def prefixEnd_6815548 : Nat := 4983230072969 + 3 ^ 40 * 6815548 * 2
def baseEnd_6815548 : Nat := 1166550682596535123601957

theorem tailTrace_6815548 : CollatzResearch.WordTrace tailWord_6815548 prefixEnd_6815548 1166550682596535123601957 := by
  unfold tailWord_6815548
  simp only [CollatzResearch.WordTrace]
  refine ⟨124291728756220536886251649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165722305008294049181668865 124291728756220536886251649)
  ·
    refine ⟨93218796567165402664688737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124291728756220536886251649 93218796567165402664688737)
    ·
      refine ⟨69914097425374051998516553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93218796567165402664688737 69914097425374051998516553)
      ·
        refine ⟨52435573069030538998887415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69914097425374051998516553 52435573069030538998887415)
        ·
          refine ⟨78653359603545808498331123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52435573069030538998887415 78653359603545808498331123)
          ·
            refine ⟨117980039405318712747496685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78653359603545808498331123 117980039405318712747496685)
            ·
              refine ⟨44242514776994517280311257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117980039405318712747496685 44242514776994517280311257)
              ·
                refine ⟨33181886082745887960233443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44242514776994517280311257 33181886082745887960233443)
                ·
                  refine ⟨49772829124118831940350165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33181886082745887960233443 49772829124118831940350165)
                  ·
                    refine ⟨1166550682596535123601957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49772829124118831940350165 1166550682596535123601957)
                    ·
                      rfl

theorem cell23_6815548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_6815548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815548 prefixEnd_6815548 := by exact prefixLift 6815548
  have htrace : WordTrace (prefixWord ++ tailWord_6815548) baseStart_6815548 baseEnd_6815548 := by
    simpa [prefixWord, tailWord_6815548, baseEnd_6815548] using wordTrace_append hprefix tailTrace_6815548
  have hstable : (prefixWord ++ tailWord_6815548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815548).length < 2 ^ (prefixWord ++ tailWord_6815548).sum := by decide
  have hdescent : baseEnd_6815548 < baseStart_6815548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815585 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_6815585 : Nat := 118140960795 + 6815585 * 2 ^ 59
def prefixEnd_6815585 : Nat := 4983230072969 + 3 ^ 40 * 6815585 * 2
def baseEnd_6815585 : Nat := 3499671046573821726043201

theorem tailTrace_6815585 : CollatzResearch.WordTrace tailWord_6815585 prefixEnd_6815585 3499671046573821726043201 := by
  unfold tailWord_6815585
  simp only [CollatzResearch.WordTrace]
  refine ⟨248584807013307029091600209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165723204675538019394400139 248584807013307029091600209)
  ·
    refine ⟨186438605259980271818700157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248584807013307029091600209 186438605259980271818700157)
    ·
      refine ⟨69914476972492601932012559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186438605259980271818700157 69914476972492601932012559)
      ·
        refine ⟨104871715458738902898018839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69914476972492601932012559 104871715458738902898018839)
        ·
          refine ⟨157307573188108354347028259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104871715458738902898018839 157307573188108354347028259)
          ·
            refine ⟨235961359782162531520542389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157307573188108354347028259 235961359782162531520542389)
            ·
              refine ⟨22121377479577737330050849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235961359782162531520542389 22121377479577737330050849)
              ·
                refine ⟨16591033109683302997538137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22121377479577737330050849 16591033109683302997538137)
                ·
                  refine ⟨12443274832262477248153603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16591033109683302997538137 12443274832262477248153603)
                  ·
                    refine ⟨18664912248393715872230405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12443274832262477248153603 18664912248393715872230405)
                    ·
                      refine ⟨3499671046573821726043201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18664912248393715872230405 3499671046573821726043201)
                      ·
                        rfl

theorem cell23_6815585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_6815585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815585 prefixEnd_6815585 := by exact prefixLift 6815585
  have htrace : WordTrace (prefixWord ++ tailWord_6815585) baseStart_6815585 baseEnd_6815585 := by
    simpa [prefixWord, tailWord_6815585, baseEnd_6815585] using wordTrace_append hprefix tailTrace_6815585
  have hstable : (prefixWord ++ tailWord_6815585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815585).length < 2 ^ (prefixWord ++ tailWord_6815585).sum := by decide
  have hdescent : baseEnd_6815585 < baseStart_6815585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815628 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6815628 : Nat := 118140960795 + 6815628 * 2 ^ 59
def prefixEnd_6815628 : Nat := 4983230072969 + 3 ^ 40 * 6815628 * 2
def baseEnd_6815628 : Nat := 3499693126241965057805503

theorem tailTrace_6815628 : CollatzResearch.WordTrace tailWord_6815628 prefixEnd_6815628 3499693126241965057805503 := by
  unfold tailWord_6815628
  simp only [CollatzResearch.WordTrace]
  refine ⟨124293187676075623717707769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165724250234767498290277025 124293187676075623717707769)
  ·
    refine ⟨93219890757056717788280827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124293187676075623717707769 93219890757056717788280827)
    ·
      refine ⟨139829836135585076682421241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93219890757056717788280827 139829836135585076682421241)
      ·
        refine ⟨104872377101688807511815931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139829836135585076682421241 104872377101688807511815931)
        ·
          refine ⟨157308565652533211267723897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104872377101688807511815931 157308565652533211267723897)
          ·
            refine ⟨117981424239399908450792923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157308565652533211267723897 117981424239399908450792923)
            ·
              refine ⟨176972136359099862676189385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117981424239399908450792923 176972136359099862676189385)
              ·
                refine ⟨132729102269324897007142039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176972136359099862676189385 132729102269324897007142039)
                ·
                  refine ⟨199093653403987345510713059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132729102269324897007142039 199093653403987345510713059)
                  ·
                    refine ⟨298640480105981018266069589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199093653403987345510713059 298640480105981018266069589)
                    ·
                      refine ⟨3499693126241965057805503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 298640480105981018266069589 3499693126241965057805503)
                      ·
                        rfl

theorem cell23_6815628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6815628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815628 prefixEnd_6815628 := by exact prefixLift 6815628
  have htrace : WordTrace (prefixWord ++ tailWord_6815628) baseStart_6815628 baseEnd_6815628 := by
    simpa [prefixWord, tailWord_6815628, baseEnd_6815628] using wordTrace_append hprefix tailTrace_6815628
  have hstable : (prefixWord ++ tailWord_6815628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815628).length < 2 ^ (prefixWord ++ tailWord_6815628).sum := by decide
  have hdescent : baseEnd_6815628 < baseStart_6815628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815642 : List Nat := [3, 1, 1, 4, 2, 2, 2, 2, 6]
def baseStart_6815642 : Nat := 118140960795 + 6815642 * 2 ^ 59
def prefixEnd_6815642 : Nat := 4983230072969 + 3 ^ 40 * 6815642 * 2
def baseEnd_6815642 : Nat := 388855590552347555892271

theorem tailTrace_6815642 : CollatzResearch.WordTrace tailWord_6815642 prefixEnd_6815642 388855590552347555892271 := by
  unfold tailWord_6815642
  simp only [CollatzResearch.WordTrace]
  refine ⟨62146721493525131956606295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165724590649400351884283453 62146721493525131956606295)
  ·
    refine ⟨93220082240287697934909443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62146721493525131956606295 93220082240287697934909443)
    ·
      refine ⟨139830123360431546902364165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93220082240287697934909443 139830123360431546902364165)
      ·
        refine ⟨26218148130080915044193281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139830123360431546902364165 26218148130080915044193281)
        ·
          refine ⟨19663611097560686283144961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26218148130080915044193281 19663611097560686283144961)
          ·
            refine ⟨14747708323170514712358721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19663611097560686283144961 14747708323170514712358721)
            ·
              refine ⟨11060781242377886034269041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747708323170514712358721 11060781242377886034269041)
              ·
                refine ⟨8295585931783414525701781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11060781242377886034269041 8295585931783414525701781)
                ·
                  refine ⟨388855590552347555892271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8295585931783414525701781 388855590552347555892271)
                  ·
                    rfl

theorem cell23_6815642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_6815642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815642 prefixEnd_6815642 := by exact prefixLift 6815642
  have htrace : WordTrace (prefixWord ++ tailWord_6815642) baseStart_6815642 baseEnd_6815642 := by
    simpa [prefixWord, tailWord_6815642, baseEnd_6815642] using wordTrace_append hprefix tailTrace_6815642
  have hstable : (prefixWord ++ tailWord_6815642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815642).length < 2 ^ (prefixWord ++ tailWord_6815642).sum := by decide
  have hdescent : baseEnd_6815642 < baseStart_6815642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815669 : List Nat := [1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_6815669 : Nat := 118140960795 + 6815669 * 2 ^ 59
def prefixEnd_6815669 : Nat := 4983230072969 + 3 ^ 40 * 6815669 * 2
def baseEnd_6815669 : Nat := 3499714178948799397392815

theorem tailTrace_6815669 : CollatzResearch.WordTrace tailWord_6815669 prefixEnd_6815669 3499714178948799397392815 := by
  unfold tailWord_6815669
  simp only [CollatzResearch.WordTrace]
  refine ⟨248587870745002711437658061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165725247163335140958438707 248587870745002711437658061)
  ·
    refine ⟨93220451529376016789121773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248587870745002711437658061 93220451529376016789121773)
    ·
      refine ⟨34957669323516006295920665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93220451529376016789121773 34957669323516006295920665)
      ·
        refine ⟨26218251992637004721940499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34957669323516006295920665 26218251992637004721940499)
        ·
          refine ⟨39327377988955507082910749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26218251992637004721940499 39327377988955507082910749)
          ·
            refine ⟨14747766745858315156091531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39327377988955507082910749 14747766745858315156091531)
            ·
              refine ⟨22121650118787472734137297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14747766745858315156091531 22121650118787472734137297)
              ·
                refine ⟨16591237589090604550602973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22121650118787472734137297 16591237589090604550602973)
                ·
                  refine ⟨6221714095908976706476115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16591237589090604550602973 6221714095908976706476115)
                  ·
                    refine ⟨9332571143863465059714173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6221714095908976706476115 9332571143863465059714173)
                    ·
                      refine ⟨3499714178948799397392815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9332571143863465059714173 3499714178948799397392815)
                      ·
                        rfl

theorem cell23_6815669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_6815669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815669 prefixEnd_6815669 := by exact prefixLift 6815669
  have htrace : WordTrace (prefixWord ++ tailWord_6815669) baseStart_6815669 baseEnd_6815669 := by
    simpa [prefixWord, tailWord_6815669, baseEnd_6815669] using wordTrace_append hprefix tailTrace_6815669
  have hstable : (prefixWord ++ tailWord_6815669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815669).length < 2 ^ (prefixWord ++ tailWord_6815669).sum := by decide
  have hdescent : baseEnd_6815669 < baseStart_6815669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815695 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 5]
def baseStart_6815695 : Nat := 118140960795 + 6815695 * 2 ^ 59
def prefixEnd_6815695 : Nat := 4983230072969 + 3 ^ 40 * 6815695 * 2
def baseEnd_6815695 : Nat := 3499727529445816295667695

theorem tailTrace_6815695 : CollatzResearch.WordTrace tailWord_6815695 prefixEnd_6815695 3499727529445816295667695 := by
  unfold tailWord_6815695
  simp only [CollatzResearch.WordTrace]
  refine ⟨248588819042908517878104539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165725879361939011918736359 248588819042908517878104539)
  ·
    refine ⟨372883228564362776817156809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248588819042908517878104539 372883228564362776817156809)
    ·
      refine ⟨279662421423272082612867607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372883228564362776817156809 279662421423272082612867607)
      ·
        refine ⟨419493632134908123919301411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279662421423272082612867607 419493632134908123919301411)
        ·
          refine ⟨629240448202362185878952117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419493632134908123919301411 629240448202362185878952117)
          ·
            refine ⟨58991292018971454926151761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 629240448202362185878952117 58991292018971454926151761)
            ·
              refine ⟨44243469014228591194613821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58991292018971454926151761 44243469014228591194613821)
              ·
                refine ⟨16591300880335721697980183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44243469014228591194613821 16591300880335721697980183)
                ·
                  refine ⟨24886951320503582546970275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16591300880335721697980183 24886951320503582546970275)
                  ·
                    refine ⟨37330426980755373820455413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24886951320503582546970275 37330426980755373820455413)
                    ·
                      refine ⟨3499727529445816295667695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37330426980755373820455413 3499727529445816295667695)
                      ·
                        rfl

theorem cell23_6815695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_6815695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815695 prefixEnd_6815695 := by exact prefixLift 6815695
  have htrace : WordTrace (prefixWord ++ tailWord_6815695) baseStart_6815695 baseEnd_6815695 := by
    simpa [prefixWord, tailWord_6815695, baseEnd_6815695] using wordTrace_append hprefix tailTrace_6815695
  have hstable : (prefixWord ++ tailWord_6815695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815695).length < 2 ^ (prefixWord ++ tailWord_6815695).sum := by decide
  have hdescent : baseEnd_6815695 < baseStart_6815695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815719 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 1, 6]
def baseStart_6815719 : Nat := 118140960795 + 6815719 * 2 ^ 59
def prefixEnd_6815719 : Nat := 4983230072969 + 3 ^ 40 * 6815719 * 2
def baseEnd_6815719 : Nat := 1166579950993841400589195

theorem tailTrace_6815719 : CollatzResearch.WordTrace tailWord_6815719 prefixEnd_6815719 1166579950993841400589195 := by
  unfold tailWord_6815719
  simp only [CollatzResearch.WordTrace]
  refine ⟨248589694394821569976978211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165726462929881046651318807 248589694394821569976978211)
  ·
    refine ⟨372884541592232354965467317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248589694394821569976978211 372884541592232354965467317)
    ·
      refine ⟨34957925774271783278012561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 372884541592232354965467317 34957925774271783278012561)
      ·
        refine ⟨26218444330703837458509421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34957925774271783278012561 26218444330703837458509421)
        ·
          refine ⟨9831916624013939046941033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26218444330703837458509421 9831916624013939046941033)
          ·
            refine ⟨7373937468010454285205775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9831916624013939046941033 7373937468010454285205775)
            ·
              refine ⟨11060906202015681427808663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7373937468010454285205775 11060906202015681427808663)
              ·
                refine ⟨16591359303023522141712995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11060906202015681427808663 16591359303023522141712995)
                ·
                  refine ⟨24887038954535283212569493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16591359303023522141712995 24887038954535283212569493)
                  ·
                    refine ⟨1166579950993841400589195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24887038954535283212569493 1166579950993841400589195)
                    ·
                      rfl

theorem cell23_6815719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_6815719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815719 prefixEnd_6815719 := by exact prefixLift 6815719
  have htrace : WordTrace (prefixWord ++ tailWord_6815719) baseStart_6815719 baseEnd_6815719 := by
    simpa [prefixWord, tailWord_6815719, baseEnd_6815719] using wordTrace_append hprefix tailTrace_6815719
  have hstable : (prefixWord ++ tailWord_6815719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815719).length < 2 ^ (prefixWord ++ tailWord_6815719).sum := by decide
  have hdescent : baseEnd_6815719 < baseStart_6815719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815726 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_6815726 : Nat := 118140960795 + 6815726 * 2 ^ 59
def prefixEnd_6815726 : Nat := 4983230072969 + 3 ^ 40 * 6815726 * 2
def baseEnd_6815726 : Nat := 3499743447346105674380053

theorem tailTrace_6815726 : CollatzResearch.WordTrace tailWord_6815726 prefixEnd_6815726 3499743447346105674380053 := by
  unfold tailWord_6815726
  simp only [CollatzResearch.WordTrace]
  refine ⟨31073743713224526271560379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165726633137197473448322021 31073743713224526271560379)
  ·
    refine ⟨46610615569836789407340569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31073743713224526271560379 46610615569836789407340569)
    ·
      refine ⟨34957961677377592055505427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46610615569836789407340569 34957961677377592055505427)
      ·
        refine ⟨52436942516066388083258141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34957961677377592055505427 52436942516066388083258141)
        ·
          refine ⟨19663853443524895531221803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52436942516066388083258141 19663853443524895531221803)
          ·
            refine ⟨29495780165287343296832705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19663853443524895531221803 29495780165287343296832705)
            ·
              refine ⟨22121835123965507472624529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29495780165287343296832705 22121835123965507472624529)
              ·
                refine ⟨16591376342974130604468397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22121835123965507472624529 16591376342974130604468397)
                ·
                  refine ⟨6221766128615298976675649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16591376342974130604468397 6221766128615298976675649)
                  ·
                    refine ⟨4666324596461474232506737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6221766128615298976675649 4666324596461474232506737)
                    ·
                      refine ⟨3499743447346105674380053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666324596461474232506737 3499743447346105674380053)
                      ·
                        rfl

theorem cell23_6815726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_6815726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815726 prefixEnd_6815726 := by exact prefixLift 6815726
  have htrace : WordTrace (prefixWord ++ tailWord_6815726) baseStart_6815726 baseEnd_6815726 := by
    simpa [prefixWord, tailWord_6815726, baseEnd_6815726] using wordTrace_append hprefix tailTrace_6815726
  have hstable : (prefixWord ++ tailWord_6815726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815726).length < 2 ^ (prefixWord ++ tailWord_6815726).sum := by decide
  have hdescent : baseEnd_6815726 < baseStart_6815726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815755 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5]
def baseStart_6815755 : Nat := 118140960795 + 6815755 * 2 ^ 59
def prefixEnd_6815755 : Nat := 4983230072969 + 3 ^ 40 * 6815755 * 2
def baseEnd_6815755 : Nat := 3499758338285086060917419

theorem tailTrace_6815755 : CollatzResearch.WordTrace tailWord_6815755 prefixEnd_6815755 3499758338285086060917419 := by
  unfold tailWord_6815755
  simp only [CollatzResearch.WordTrace]
  refine ⟨248591007422691148125288719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165727338281794098750192479 248591007422691148125288719)
  ·
    refine ⟨372886511134036722187933079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248591007422691148125288719 372886511134036722187933079)
    ·
      refine ⟨559329766701055083281899619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372886511134036722187933079 559329766701055083281899619)
      ·
        refine ⟨838994650051582624922849429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559329766701055083281899619 838994650051582624922849429)
        ·
          refine ⟨39327874221167935543258567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 838994650051582624922849429 39327874221167935543258567)
          ·
            refine ⟨58991811331751903314887851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39327874221167935543258567 58991811331751903314887851)
            ·
              refine ⟨88487716997627854972331777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58991811331751903314887851 88487716997627854972331777)
              ·
                refine ⟨66365787748220891229248833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88487716997627854972331777 66365787748220891229248833)
                ·
                  refine ⟨49774340811165668421936625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66365787748220891229248833 49774340811165668421936625)
                  ·
                    refine ⟨37330755608374251316452469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49774340811165668421936625 37330755608374251316452469)
                    ·
                      refine ⟨3499758338285086060917419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37330755608374251316452469 3499758338285086060917419)
                      ·
                        rfl

theorem cell23_6815755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 5].length) (baseStart_6815755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815755 prefixEnd_6815755 := by exact prefixLift 6815755
  have htrace : WordTrace (prefixWord ++ tailWord_6815755) baseStart_6815755 baseEnd_6815755 := by
    simpa [prefixWord, tailWord_6815755, baseEnd_6815755] using wordTrace_append hprefix tailTrace_6815755
  have hstable : (prefixWord ++ tailWord_6815755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815755).length < 2 ^ (prefixWord ++ tailWord_6815755).sum := by decide
  have hdescent : baseEnd_6815755 < baseStart_6815755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815775 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 8]
def baseStart_6815775 : Nat := 118140960795 + 6815775 * 2 ^ 59
def prefixEnd_6815775 : Nat := 4983230072969 + 3 ^ 40 * 6815775 * 2
def baseEnd_6815775 : Nat := 1166589535966058660889109

theorem tailTrace_6815775 : CollatzResearch.WordTrace tailWord_6815775 prefixEnd_6815775 1166589535966058660889109 := by
  unfold tailWord_6815775
  simp only [CollatzResearch.WordTrace]
  refine ⟨248591736882618691541016779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165727824588412461027344519 248591736882618691541016779)
  ·
    refine ⟨372887605323928037311525169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248591736882618691541016779 372887605323928037311525169)
    ·
      refine ⟨279665703992946027983643877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372887605323928037311525169 279665703992946027983643877)
      ·
        refine ⟨52437319498677380246933227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279665703992946027983643877 52437319498677380246933227)
        ·
          refine ⟨78655979248016070370399841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52437319498677380246933227 78655979248016070370399841)
          ·
            refine ⟨58991984436012052777799881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78655979248016070370399841 58991984436012052777799881)
            ·
              refine ⟨44243988327009039583349911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58991984436012052777799881 44243988327009039583349911)
              ·
                refine ⟨66365982490513559375024867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44243988327009039583349911 66365982490513559375024867)
                ·
                  refine ⟨99548973735770339062537301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66365982490513559375024867 99548973735770339062537301)
                  ·
                    refine ⟨1166589535966058660889109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99548973735770339062537301 1166589535966058660889109)
                    ·
                      rfl

theorem cell23_6815775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 8].length) (baseStart_6815775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815775 prefixEnd_6815775 := by exact prefixLift 6815775
  have htrace : WordTrace (prefixWord ++ tailWord_6815775) baseStart_6815775 baseEnd_6815775 := by
    simpa [prefixWord, tailWord_6815775, baseEnd_6815775] using wordTrace_append hprefix tailTrace_6815775
  have hstable : (prefixWord ++ tailWord_6815775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815775).length < 2 ^ (prefixWord ++ tailWord_6815775).sum := by decide
  have hdescent : baseEnd_6815775 < baseStart_6815775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815786 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_6815786 : Nat := 118140960795 + 6815786 * 2 ^ 59
def prefixEnd_6815786 : Nat := 4983230072969 + 3 ^ 40 * 6815786 * 2
def baseEnd_6815786 : Nat := 3499774256185375439629777

theorem tailTrace_6815786 : CollatzResearch.WordTrace tailWord_6815786 prefixEnd_6815786 3499774256185375439629777 := by
  unfold tailWord_6815786
  simp only [CollatzResearch.WordTrace]
  refine ⟨62148034521394710104916803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165728092057052560279778141 62148034521394710104916803)
  ·
    refine ⟨93222051782092065157375205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62148034521394710104916803 93222051782092065157375205)
    ·
      refine ⟨17479134709142262217007851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93222051782092065157375205 17479134709142262217007851)
      ·
        refine ⟨26218702063713393325511777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17479134709142262217007851 26218702063713393325511777)
        ·
          refine ⟨19664026547785044994133833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26218702063713393325511777 19664026547785044994133833)
          ·
            refine ⟨14748019910838783745600375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19664026547785044994133833 14748019910838783745600375)
            ·
              refine ⟨22122029866258175618400563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14748019910838783745600375 22122029866258175618400563)
              ·
                refine ⟨33183044799387263427600845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22122029866258175618400563 33183044799387263427600845)
                ·
                  refine ⟨12443641799770223785350317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33183044799387263427600845 12443641799770223785350317)
                  ·
                    refine ⟨4666365674913833919506369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12443641799770223785350317 4666365674913833919506369)
                    ·
                      refine ⟨3499774256185375439629777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666365674913833919506369 3499774256185375439629777)
                      ·
                        rfl

theorem cell23_6815786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_6815786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815786 prefixEnd_6815786 := by exact prefixLift 6815786
  have htrace : WordTrace (prefixWord ++ tailWord_6815786) baseStart_6815786 baseEnd_6815786 := by
    simpa [prefixWord, tailWord_6815786, baseEnd_6815786] using wordTrace_append hprefix tailTrace_6815786
  have hstable : (prefixWord ++ tailWord_6815786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815786).length < 2 ^ (prefixWord ++ tailWord_6815786).sum := by decide
  have hdescent : baseEnd_6815786 < baseStart_6815786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815799 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 6, 2, 2]
def baseStart_6815799 : Nat := 118140960795 + 6815799 * 2 ^ 59
def prefixEnd_6815799 : Nat := 4983230072969 + 3 ^ 40 * 6815799 * 2
def baseEnd_6815799 : Nat := 3499780931433883888767217

theorem tailTrace_6815799 : CollatzResearch.WordTrace tailWord_6815799 prefixEnd_6815799 3499780931433883888767217 := by
  unfold tailWord_6815799
  simp only [CollatzResearch.WordTrace]
  refine ⟨248592612234531743639890451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165728408156354495759926967 248592612234531743639890451)
  ·
    refine ⟨372888918351797615459835677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248592612234531743639890451 372888918351797615459835677)
    ·
      refine ⟨139833344381924105797438379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372888918351797615459835677 139833344381924105797438379)
      ·
        refine ⟨209750016572886158696157569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139833344381924105797438379 209750016572886158696157569)
        ·
          refine ⟨157312512429664619022118177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209750016572886158696157569 157312512429664619022118177)
          ·
            refine ⟨117984384322248464266588633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157312512429664619022118177 117984384322248464266588633)
            ·
              refine ⟨88488288241686348199941475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117984384322248464266588633 88488288241686348199941475)
              ·
                refine ⟨132732432362529522299912213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88488288241686348199941475 132732432362529522299912213)
                ·
                  refine ⟨6221832766993571357808385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132732432362529522299912213 6221832766993571357808385)
                  ·
                    refine ⟨4666374575245178518356289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6221832766993571357808385 4666374575245178518356289)
                    ·
                      refine ⟨3499780931433883888767217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666374575245178518356289 3499780931433883888767217)
                      ·
                        rfl

theorem cell23_6815799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 2, 2].length) (baseStart_6815799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815799 prefixEnd_6815799 := by exact prefixLift 6815799
  have htrace : WordTrace (prefixWord ++ tailWord_6815799) baseStart_6815799 baseEnd_6815799 := by
    simpa [prefixWord, tailWord_6815799, baseEnd_6815799] using wordTrace_append hprefix tailTrace_6815799
  have hstable : (prefixWord ++ tailWord_6815799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815799).length < 2 ^ (prefixWord ++ tailWord_6815799).sum := by decide
  have hdescent : baseEnd_6815799 < baseStart_6815799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815825 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_6815825 : Nat := 118140960795 + 6815825 * 2 ^ 59
def prefixEnd_6815825 : Nat := 4983230072969 + 3 ^ 40 * 6815825 * 2
def baseEnd_6815825 : Nat := 3499794281930900787042097

theorem tailTrace_6815825 : CollatzResearch.WordTrace tailWord_6815825 prefixEnd_6815825 3499794281930900787042097 := by
  unfold tailWord_6815825
  simp only [CollatzResearch.WordTrace]
  refine ⟨248593560532437550080336929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165729040354958366720224619 248593560532437550080336929)
  ·
    refine ⟨186445170399328162560252697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248593560532437550080336929 186445170399328162560252697)
    ·
      refine ⟨139833877799496121920189523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186445170399328162560252697 139833877799496121920189523)
      ·
        refine ⟨209750816699244182880284285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139833877799496121920189523 209750816699244182880284285)
        ·
          refine ⟨78656556262216568580106607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209750816699244182880284285 78656556262216568580106607)
          ·
            refine ⟨117984834393324852870159911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78656556262216568580106607 117984834393324852870159911)
            ·
              refine ⟨176977251589987279305239867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117984834393324852870159911 176977251589987279305239867)
              ·
                refine ⟨265465877384980918957859801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176977251589987279305239867 265465877384980918957859801)
                ·
                  refine ⟨199099408038735689218394851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265465877384980918957859801 199099408038735689218394851)
                  ·
                    refine ⟨298649112058103533827592277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 199099408038735689218394851 298649112058103533827592277)
                    ·
                      refine ⟨3499794281930900787042097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 298649112058103533827592277 3499794281930900787042097)
                      ·
                        rfl

theorem cell23_6815825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_6815825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815825 prefixEnd_6815825 := by exact prefixLift 6815825
  have htrace : WordTrace (prefixWord ++ tailWord_6815825) baseStart_6815825 baseEnd_6815825 := by
    simpa [prefixWord, tailWord_6815825, baseEnd_6815825] using wordTrace_append hprefix tailTrace_6815825
  have hstable : (prefixWord ++ tailWord_6815825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815825).length < 2 ^ (prefixWord ++ tailWord_6815825).sum := by decide
  have hdescent : baseEnd_6815825 < baseStart_6815825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815832 : List Nat := [2, 1, 2, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_6815832 : Nat := 118140960795 + 6815832 * 2 ^ 59
def prefixEnd_6815832 : Nat := 4983230072969 + 3 ^ 40 * 6815832 * 2
def baseEnd_6815832 : Nat := 3499797876295482259654565

theorem tailTrace_6815832 : CollatzResearch.WordTrace tailWord_6815832 prefixEnd_6815832 3499797876295482259654565 := by
  unfold tailWord_6815832
  simp only [CollatzResearch.WordTrace]
  refine ⟨124296907921706095137920875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165729210562274793517227833 124296907921706095137920875)
  ·
    refine ⟨186445361882559142706881313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124296907921706095137920875 186445361882559142706881313)
    ·
      refine ⟨139834021411919357030160985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186445361882559142706881313 139834021411919357030160985)
      ·
        refine ⟨104875516058939517772620739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139834021411919357030160985 104875516058939517772620739)
        ·
          refine ⟨157313274088409276658931109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104875516058939517772620739 157313274088409276658931109)
          ·
            refine ⟨29496238891576739373549583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157313274088409276658931109 29496238891576739373549583)
            ·
              refine ⟨44244358337365109060324375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29496238891576739373549583 44244358337365109060324375)
              ·
                refine ⟨66366537506047663590486563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44244358337365109060324375 66366537506047663590486563)
                ·
                  refine ⟨99549806259071495385729845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66366537506047663590486563 99549806259071495385729845)
                  ·
                    refine ⟨9332794336787952692412173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99549806259071495385729845 9332794336787952692412173)
                    ·
                      refine ⟨3499797876295482259654565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9332794336787952692412173 3499797876295482259654565)
                      ·
                        rfl

theorem cell23_6815832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_6815832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815832 prefixEnd_6815832 := by exact prefixLift 6815832
  have htrace : WordTrace (prefixWord ++ tailWord_6815832) baseStart_6815832 baseEnd_6815832 := by
    simpa [prefixWord, tailWord_6815832, baseEnd_6815832] using wordTrace_append hprefix tailTrace_6815832
  have hstable : (prefixWord ++ tailWord_6815832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815832).length < 2 ^ (prefixWord ++ tailWord_6815832).sum := by decide
  have hdescent : baseEnd_6815832 < baseStart_6815832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815852 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 1, 7]
def baseStart_6815852 : Nat := 118140960795 + 6815852 * 2 ^ 59
def prefixEnd_6815852 : Nat := 4983230072969 + 3 ^ 40 * 6815852 * 2
def baseEnd_6815852 : Nat := 1166602715302857393801491

theorem tailTrace_6815852 : CollatzResearch.WordTrace tailWord_6815852 prefixEnd_6815852 1166602715302857393801491 := by
  unfold tailWord_6815852
  simp only [CollatzResearch.WordTrace]
  refine ⟨124297272651669866845784905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165729696868893155794379873 124297272651669866845784905)
  ·
    refine ⟨93222954488752400134338679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124297272651669866845784905 93222954488752400134338679)
    ·
      refine ⟨139834431733128600201508019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93222954488752400134338679 139834431733128600201508019)
      ·
        refine ⟨209751647599692900302262029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139834431733128600201508019 209751647599692900302262029)
        ·
          refine ⟨78656867849884837613348261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209751647599692900302262029 78656867849884837613348261)
          ·
            refine ⟨14748162721853407052502799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78656867849884837613348261 14748162721853407052502799)
            ·
              refine ⟨22122244082780110578754199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14748162721853407052502799 22122244082780110578754199)
              ·
                refine ⟨33183366124170165868131299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22122244082780110578754199 33183366124170165868131299)
                ·
                  refine ⟨49775049186255248802196949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33183366124170165868131299 49775049186255248802196949)
                  ·
                    refine ⟨1166602715302857393801491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49775049186255248802196949 1166602715302857393801491)
                    ·
                      rfl

theorem cell23_6815852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_6815852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815852 prefixEnd_6815852 := by exact prefixLift 6815852
  have htrace : WordTrace (prefixWord ++ tailWord_6815852) baseStart_6815852 baseEnd_6815852 := by
    simpa [prefixWord, tailWord_6815852, baseEnd_6815852] using wordTrace_append hprefix tailTrace_6815852
  have hstable : (prefixWord ++ tailWord_6815852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815852).length < 2 ^ (prefixWord ++ tailWord_6815852).sum := by decide
  have hdescent : baseEnd_6815852 < baseStart_6815852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815872 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_6815872 : Nat := 118140960795 + 6815872 * 2 ^ 59
def prefixEnd_6815872 : Nat := 4983230072969 + 3 ^ 40 * 6815872 * 2
def baseEnd_6815872 : Nat := 3499818415521662103154381

theorem tailTrace_6815872 : CollatzResearch.WordTrace tailWord_6815872 prefixEnd_6815872 3499818415521662103154381 := by
  unfold tailWord_6815872
  simp only [CollatzResearch.WordTrace]
  refine ⟨124297637381633638553648935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165730183175511518071531913 124297637381633638553648935)
  ·
    refine ⟨186446456072450457830473403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124297637381633638553648935 186446456072450457830473403)
    ·
      refine ⟨279669684108675686745710105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186446456072450457830473403 279669684108675686745710105)
      ·
        refine ⟨209752263081506765059282579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279669684108675686745710105 209752263081506765059282579)
        ·
          refine ⟨314628394622260147588923869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209752263081506765059282579 314628394622260147588923869)
          ·
            refine ⟨117985647983347555345846451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314628394622260147588923869 117985647983347555345846451)
            ·
              refine ⟨176978471975021333018769677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117985647983347555345846451 176978471975021333018769677)
              ·
                refine ⟨66366926990632999882038629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176978471975021333018769677 66366926990632999882038629)
                ·
                  refine ⟨12443798810743687477882243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66366926990632999882038629 12443798810743687477882243)
                  ·
                    refine ⟨18665698216115531216823365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12443798810743687477882243 18665698216115531216823365)
                    ·
                      refine ⟨3499818415521662103154381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18665698216115531216823365 3499818415521662103154381)
                      ·
                        rfl

theorem cell23_6815872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_6815872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815872 prefixEnd_6815872 := by exact prefixLift 6815872
  have htrace : WordTrace (prefixWord ++ tailWord_6815872) baseStart_6815872 baseEnd_6815872 := by
    simpa [prefixWord, tailWord_6815872, baseEnd_6815872] using wordTrace_append hprefix tailTrace_6815872
  have hstable : (prefixWord ++ tailWord_6815872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815872).length < 2 ^ (prefixWord ++ tailWord_6815872).sum := by decide
  have hdescent : baseEnd_6815872 < baseStart_6815872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815909 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_6815909 : Nat := 118140960795 + 6815909 * 2 ^ 59
def prefixEnd_6815909 : Nat := 4983230072969 + 3 ^ 40 * 6815909 * 2
def baseEnd_6815909 : Nat := 3499837414305878458391711

theorem tailTrace_6815909 : CollatzResearch.WordTrace tailWord_6815909 prefixEnd_6815909 3499837414305878458391711 := by
  unfold tailWord_6815909
  simp only [CollatzResearch.WordTrace]
  refine ⟨248596624264133232426394781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165731082842755488284263187 248596624264133232426394781)
  ·
    refine ⟨93223734099049962159898043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248596624264133232426394781 93223734099049962159898043)
    ·
      refine ⟨139835601148574943239847065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93223734099049962159898043 139835601148574943239847065)
      ·
        refine ⟨104876700861431207429885299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139835601148574943239847065 104876700861431207429885299)
        ·
          refine ⟨157315051292146811144827949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104876700861431207429885299 157315051292146811144827949)
          ·
            refine ⟨58993144234555054179310481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157315051292146811144827949 58993144234555054179310481)
            ·
              refine ⟨44244858175916290634482861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58993144234555054179310481 44244858175916290634482861)
              ·
                refine ⟨16591821815968608987931073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44244858175916290634482861 16591821815968608987931073)
                ·
                  refine ⟨12443866361976456740948305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16591821815968608987931073 12443866361976456740948305)
                  ·
                    refine ⟨9332899771482342555711229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12443866361976456740948305 9332899771482342555711229)
                    ·
                      refine ⟨3499837414305878458391711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9332899771482342555711229 3499837414305878458391711)
                      ·
                        rfl

theorem cell23_6815909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_6815909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815909 prefixEnd_6815909 := by exact prefixLift 6815909
  have htrace : WordTrace (prefixWord ++ tailWord_6815909) baseStart_6815909 baseEnd_6815909 := by
    simpa [prefixWord, tailWord_6815909, baseEnd_6815909] using wordTrace_append hprefix tailTrace_6815909
  have hstable : (prefixWord ++ tailWord_6815909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815909).length < 2 ^ (prefixWord ++ tailWord_6815909).sum := by decide
  have hdescent : baseEnd_6815909 < baseStart_6815909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815992 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_6815992 : Nat := 118140960795 + 6815992 * 2 ^ 59
def prefixEnd_6815992 : Nat := 4983230072969 + 3 ^ 40 * 6815992 * 2
def baseEnd_6815992 : Nat := 3499880033200201633653829

theorem tailTrace_6815992 : CollatzResearch.WordTrace tailWord_6815992 prefixEnd_6815992 3499880033200201633653829 := by
  unfold tailWord_6815992
  simp only [CollatzResearch.WordTrace]
  refine ⟨124299825761416268800833115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165733101015221691734444153 124299825761416268800833115)
  ·
    refine ⟨186449738642124403201249673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124299825761416268800833115 186449738642124403201249673)
    ·
      refine ⟨139837303981593302400937255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186449738642124403201249673 139837303981593302400937255)
      ·
        refine ⟨209755955972389953601405883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139837303981593302400937255 209755955972389953601405883)
        ·
          refine ⟨314633933958584930402108825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209755955972389953601405883 314633933958584930402108825)
          ·
            refine ⟨235975450468938697801581619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314633933958584930402108825 235975450468938697801581619)
            ·
              refine ⟨353963175703408046702372429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235975450468938697801581619 353963175703408046702372429)
              ·
                refine ⟨132736190888778017513389661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353963175703408046702372429 132736190888778017513389661)
                ·
                  refine ⟨49776071583291756567521123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132736190888778017513389661 49776071583291756567521123)
                  ·
                    refine ⟨74664107374937634851281685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49776071583291756567521123 74664107374937634851281685)
                    ·
                      refine ⟨3499880033200201633653829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74664107374937634851281685 3499880033200201633653829)
                      ·
                        rfl

theorem cell23_6815992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_6815992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815992 prefixEnd_6815992 := by exact prefixLift 6815992
  have htrace : WordTrace (prefixWord ++ tailWord_6815992) baseStart_6815992 baseEnd_6815992 := by
    simpa [prefixWord, tailWord_6815992, baseEnd_6815992] using wordTrace_append hprefix tailTrace_6815992
  have hstable : (prefixWord ++ tailWord_6815992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815992).length < 2 ^ (prefixWord ++ tailWord_6815992).sum := by decide
  have hdescent : baseEnd_6815992 < baseStart_6815992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6815999 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 3]
def baseStart_6815999 : Nat := 118140960795 + 6815999 * 2 ^ 59
def prefixEnd_6815999 : Nat := 4983230072969 + 3 ^ 40 * 6815999 * 2
def baseEnd_6815999 : Nat := 3499883627564783106266297

theorem tailTrace_6815999 : CollatzResearch.WordTrace tailWord_6815999 prefixEnd_6815999 3499883627564783106266297 := by
  unfold tailWord_6815999
  simp only [CollatzResearch.WordTrace]
  refine ⟨248599906833807177797171051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165733271222538118531447367 248599906833807177797171051)
  ·
    refine ⟨372899860250710766695756577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248599906833807177797171051 372899860250710766695756577)
    ·
      refine ⟨279674895188033075021817433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372899860250710766695756577 279674895188033075021817433)
      ·
        refine ⟨209756171391024806266363075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279674895188033075021817433 209756171391024806266363075)
        ·
          refine ⟨314634257086537209399544613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209756171391024806266363075 314634257086537209399544613)
          ·
            refine ⟨58993923203725726762414615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314634257086537209399544613 58993923203725726762414615)
            ·
              refine ⟨88490884805588590143621923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58993923203725726762414615 88490884805588590143621923)
              ·
                refine ⟨132736327208382885215432885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88490884805588590143621923 132736327208382885215432885)
                ·
                  refine ⟨12444030675785895488946833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132736327208382885215432885 12444030675785895488946833)
                  ·
                    refine ⟨9333023006839421616710125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12444030675785895488946833 9333023006839421616710125)
                    ·
                      refine ⟨3499883627564783106266297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333023006839421616710125 3499883627564783106266297)
                      ·
                        rfl

theorem cell23_6815999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 2, 3].length) (baseStart_6815999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6815999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6815999 prefixEnd_6815999 := by exact prefixLift 6815999
  have htrace : WordTrace (prefixWord ++ tailWord_6815999) baseStart_6815999 baseEnd_6815999 := by
    simpa [prefixWord, tailWord_6815999, baseEnd_6815999] using wordTrace_append hprefix tailTrace_6815999
  have hstable : (prefixWord ++ tailWord_6815999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6815999).length < 2 ^ (prefixWord ++ tailWord_6815999).sum := by decide
  have hdescent : baseEnd_6815999 < baseStart_6815999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6815999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816009 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_6816009 : Nat := 118140960795 + 6816009 * 2 ^ 59
def prefixEnd_6816009 : Nat := 4983230072969 + 3 ^ 40 * 6816009 * 2
def baseEnd_6816009 : Nat := 3499888762371328067141251

theorem tailTrace_6816009 : CollatzResearch.WordTrace tailWord_6816009 prefixEnd_6816009 3499888762371328067141251 := by
  unfold tailWord_6816009
  simp only [CollatzResearch.WordTrace]
  refine ⟨248600271563770949505035081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165733514375847299670023387 248600271563770949505035081)
  ·
    refine ⟨186450203672828212128776311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248600271563770949505035081 186450203672828212128776311)
    ·
      refine ⟨279675305509242318193164467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186450203672828212128776311 279675305509242318193164467)
      ·
        refine ⟨419512958263863477289746701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279675305509242318193164467 419512958263863477289746701)
        ·
          refine ⟨157317359348948803983655013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419512958263863477289746701 157317359348948803983655013)
          ·
            refine ⟨29497004877927900746935315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157317359348948803983655013 29497004877927900746935315)
            ·
              refine ⟨44245507316891851120402973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29497004877927900746935315 44245507316891851120402973)
              ·
                refine ⟨16592065243834444170151115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44245507316891851120402973 16592065243834444170151115)
                ·
                  refine ⟨24888097865751666255226673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16592065243834444170151115 24888097865751666255226673)
                  ·
                    refine ⟨18666073399313749691420005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24888097865751666255226673 18666073399313749691420005)
                    ·
                      refine ⟨3499888762371328067141251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18666073399313749691420005 3499888762371328067141251)
                      ·
                        rfl

theorem cell23_6816009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_6816009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816009 prefixEnd_6816009 := by exact prefixLift 6816009
  have htrace : WordTrace (prefixWord ++ tailWord_6816009) baseStart_6816009 baseEnd_6816009 := by
    simpa [prefixWord, tailWord_6816009, baseEnd_6816009] using wordTrace_append hprefix tailTrace_6816009
  have hstable : (prefixWord ++ tailWord_6816009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816009).length < 2 ^ (prefixWord ++ tailWord_6816009).sum := by decide
  have hdescent : baseEnd_6816009 < baseStart_6816009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816030 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_6816030 : Nat := 118140960795 + 6816030 * 2 ^ 59
def prefixEnd_6816030 : Nat := 4983230072969 + 3 ^ 40 * 6816030 * 2
def baseEnd_6816030 : Nat := 3499899545465072484978655

theorem tailTrace_6816030 : CollatzResearch.WordTrace tailWord_6816030 prefixEnd_6816030 3499899545465072484978655 := by
  unfold tailWord_6816030
  simp only [CollatzResearch.WordTrace]
  refine ⟨31075129687086858761443693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165734024997796580061033029 31075129687086858761443693)
  ·
    refine ⟨11653173632657572035541385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31075129687086858761443693 11653173632657572035541385)
    ·
      refine ⟨8739880224493179026656039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11653173632657572035541385 8739880224493179026656039)
      ·
        refine ⟨13109820336739768539984059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8739880224493179026656039 13109820336739768539984059)
        ·
          refine ⟨19664730505109652809976089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13109820336739768539984059 19664730505109652809976089)
          ·
            refine ⟨14748547878832239607482067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19664730505109652809976089 14748547878832239607482067)
            ·
              refine ⟨22122821818248359411223101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14748547878832239607482067 22122821818248359411223101)
              ·
                refine ⟨8296058181843134779208663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22122821818248359411223101 8296058181843134779208663)
                ·
                  refine ⟨12444087272764702168812995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296058181843134779208663 12444087272764702168812995)
                  ·
                    refine ⟨18666130909147053253219493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12444087272764702168812995 18666130909147053253219493)
                    ·
                      refine ⟨3499899545465072484978655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18666130909147053253219493 3499899545465072484978655)
                      ·
                        rfl

theorem cell23_6816030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_6816030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816030 prefixEnd_6816030 := by exact prefixLift 6816030
  have htrace : WordTrace (prefixWord ++ tailWord_6816030) baseStart_6816030 baseEnd_6816030 := by
    simpa [prefixWord, tailWord_6816030, baseEnd_6816030] using wordTrace_append hprefix tailTrace_6816030
  have hstable : (prefixWord ++ tailWord_6816030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816030).length < 2 ^ (prefixWord ++ tailWord_6816030).sum := by decide
  have hdescent : baseEnd_6816030 < baseStart_6816030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816033 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_6816033 : Nat := 118140960795 + 6816033 * 2 ^ 59
def prefixEnd_6816033 : Nat := 4983230072969 + 3 ^ 40 * 6816033 * 2
def baseEnd_6816033 : Nat := 3499901085907035973241141

theorem tailTrace_6816033 : CollatzResearch.WordTrace tailWord_6816033 prefixEnd_6816033 3499901085907035973241141 := by
  unfold tailWord_6816033
  simp only [CollatzResearch.WordTrace]
  refine ⟨248601146915684001603908753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165734097943789334402605835 248601146915684001603908753)
  ·
    refine ⟨186450860186763001202931565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248601146915684001603908753 186450860186763001202931565)
    ·
      refine ⟨69919072570036125451099337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186450860186763001202931565 69919072570036125451099337)
      ·
        refine ⟨52439304427527094088324503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69919072570036125451099337 52439304427527094088324503)
        ·
          refine ⟨78658956641290641132486755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52439304427527094088324503 78658956641290641132486755)
          ·
            refine ⟨117988434961935961698730133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78658956641290641132486755 117988434961935961698730133)
            ·
              refine ⟨5530707888840748204627975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117988434961935961698730133 5530707888840748204627975)
              ·
                refine ⟨8296061833261122306941963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530707888840748204627975 8296061833261122306941963)
                ·
                  refine ⟨12444092749891683460412945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296061833261122306941963 12444092749891683460412945)
                  ·
                    refine ⟨9333069562418762595309709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12444092749891683460412945 9333069562418762595309709)
                    ·
                      refine ⟨3499901085907035973241141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333069562418762595309709 3499901085907035973241141)
                      ·
                        rfl

theorem cell23_6816033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_6816033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816033 prefixEnd_6816033 := by exact prefixLift 6816033
  have htrace : WordTrace (prefixWord ++ tailWord_6816033) baseStart_6816033 baseEnd_6816033 := by
    simpa [prefixWord, tailWord_6816033, baseEnd_6816033] using wordTrace_append hprefix tailTrace_6816033
  have hstable : (prefixWord ++ tailWord_6816033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816033).length < 2 ^ (prefixWord ++ tailWord_6816033).sum := by decide
  have hdescent : baseEnd_6816033 < baseStart_6816033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816040 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6816040 : Nat := 118140960795 + 6816040 * 2 ^ 59
def prefixEnd_6816040 : Nat := 4983230072969 + 3 ^ 40 * 6816040 * 2
def baseEnd_6816040 : Nat := 1166634893423872481951203

theorem tailTrace_6816040 : CollatzResearch.WordTrace tailWord_6816040 prefixEnd_6816040 1166634893423872481951203 := by
  unfold tailWord_6816040
  simp only [CollatzResearch.WordTrace]
  refine ⟨124300701113329320899706787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165734268151105761199609049 124300701113329320899706787)
  ·
    refine ⟨186451051669993981349560181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124300701113329320899706787 186451051669993981349560181)
    ·
      refine ⟨17479786094061935751521267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186451051669993981349560181 17479786094061935751521267)
      ·
        refine ⟨26219679141092903627281901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17479786094061935751521267 26219679141092903627281901)
        ·
          refine ⟨9832379677909838860230713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26219679141092903627281901 9832379677909838860230713)
          ·
            refine ⟨7374284758432379145173035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9832379677909838860230713 7374284758432379145173035)
            ·
              refine ⟨11061427137648568717759553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374284758432379145173035 11061427137648568717759553)
              ·
                refine ⟨8296070353236426538319665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11061427137648568717759553 8296070353236426538319665)
                ·
                  refine ⟨6222052764927319903739749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8296070353236426538319665 6222052764927319903739749)
                  ·
                    refine ⟨1166634893423872481951203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6222052764927319903739749 1166634893423872481951203)
                    ·
                      rfl

theorem cell23_6816040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6816040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816040 prefixEnd_6816040 := by exact prefixLift 6816040
  have htrace : WordTrace (prefixWord ++ tailWord_6816040) baseStart_6816040 baseEnd_6816040 := by
    simpa [prefixWord, tailWord_6816040, baseEnd_6816040] using wordTrace_append hprefix tailTrace_6816040
  have hstable : (prefixWord ++ tailWord_6816040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816040).length < 2 ^ (prefixWord ++ tailWord_6816040).sum := by decide
  have hdescent : baseEnd_6816040 < baseStart_6816040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816056 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 5, 3, 2]
def baseStart_6816056 : Nat := 118140960795 + 6816056 * 2 ^ 59
def prefixEnd_6816056 : Nat := 4983230072969 + 3 ^ 40 * 6816056 * 2
def baseEnd_6816056 : Nat := 3499912895962089383253535

theorem tailTrace_6816056 : CollatzResearch.WordTrace tailWord_6816056 prefixEnd_6816056 3499912895962089383253535 := by
  unfold tailWord_6816056
  simp only [CollatzResearch.WordTrace]
  refine ⟨124300992897300338265998011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165734657196400451021330681 124300992897300338265998011)
  ·
    refine ⟨186451489345950507398997017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124300992897300338265998011 186451489345950507398997017)
    ·
      refine ⟨139838617009462880549247763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186451489345950507398997017 139838617009462880549247763)
      ·
        refine ⟨209757925514194320823871645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139838617009462880549247763 209757925514194320823871645)
        ·
          refine ⟨78659222067822870308951867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209757925514194320823871645 78659222067822870308951867)
          ·
            refine ⟨117988833101734305463427801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78659222067822870308951867 117988833101734305463427801)
            ·
              refine ⟨88491624826300729097570851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117988833101734305463427801 88491624826300729097570851)
              ·
                refine ⟨132737437239451093646356277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88491624826300729097570851 132737437239451093646356277)
                ·
                  refine ⟨12444134741198540029345901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132737437239451093646356277 12444134741198540029345901)
                  ·
                    refine ⟨4666550527949452511004713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12444134741198540029345901 4666550527949452511004713)
                    ·
                      refine ⟨3499912895962089383253535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666550527949452511004713 3499912895962089383253535)
                      ·
                        rfl

theorem cell23_6816056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 3, 2].length) (baseStart_6816056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816056 prefixEnd_6816056 := by exact prefixLift 6816056
  have htrace : WordTrace (prefixWord ++ tailWord_6816056) baseStart_6816056 baseEnd_6816056 := by
    simpa [prefixWord, tailWord_6816056, baseEnd_6816056] using wordTrace_append hprefix tailTrace_6816056
  have hstable : (prefixWord ++ tailWord_6816056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816056).length < 2 ^ (prefixWord ++ tailWord_6816056).sum := by decide
  have hdescent : baseEnd_6816056 < baseStart_6816056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816089 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_6816089 : Nat := 118140960795 + 6816089 * 2 ^ 59
def prefixEnd_6816089 : Nat := 4983230072969 + 3 ^ 40 * 6816089 * 2
def baseEnd_6816089 : Nat := 3499929840823687754140883

theorem tailTrace_6816089 : CollatzResearch.WordTrace tailWord_6816089 prefixEnd_6816089 3499929840823687754140883 := by
  unfold tailWord_6816089
  simp only [CollatzResearch.WordTrace]
  refine ⟨248603189403481123167947321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165735459602320748778631547 248603189403481123167947321)
  ·
    refine ⟨186452392052610842375960491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248603189403481123167947321 186452392052610842375960491)
    ·
      refine ⟨279678588078916263563940737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186452392052610842375960491 279678588078916263563940737)
      ·
        refine ⟨209758941059187197672955553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279678588078916263563940737 209758941059187197672955553)
        ·
          refine ⟨157319205794390398254716665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209758941059187197672955553 157319205794390398254716665)
          ·
            refine ⟨117989404345792798691037499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157319205794390398254716665 117989404345792798691037499)
            ·
              refine ⟨176984106518689198036556249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117989404345792798691037499 176984106518689198036556249)
              ·
                refine ⟨132738079889016898527417187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176984106518689198036556249 132738079889016898527417187)
                ·
                  refine ⟨199107119833525347791125781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132738079889016898527417187 199107119833525347791125781)
                  ·
                    refine ⟨9333146242196500677709021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 199107119833525347791125781 9333146242196500677709021)
                    ·
                      refine ⟨3499929840823687754140883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333146242196500677709021 3499929840823687754140883)
                      ·
                        rfl

theorem cell23_6816089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_6816089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816089 prefixEnd_6816089 := by exact prefixLift 6816089
  have htrace : WordTrace (prefixWord ++ tailWord_6816089) baseStart_6816089 baseEnd_6816089 := by
    simpa [prefixWord, tailWord_6816089, baseEnd_6816089] using wordTrace_append hprefix tailTrace_6816089
  have hstable : (prefixWord ++ tailWord_6816089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816089).length < 2 ^ (prefixWord ++ tailWord_6816089).sum := by decide
  have hdescent : baseEnd_6816089 < baseStart_6816089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816160 : List Nat := [2, 1, 1, 4, 1, 5, 2, 2, 5]
def baseStart_6816160 : Nat := 118140960795 + 6816160 * 2 ^ 59
def prefixEnd_6816160 : Nat := 4983230072969 + 3 ^ 40 * 6816160 * 2
def baseEnd_6816160 : Nat := 388885144216684108483673

theorem tailTrace_6816160 : CollatzResearch.WordTrace tailWord_6816160 prefixEnd_6816160 388885144216684108483673 := by
  unfold tailWord_6816160
  simp only [CollatzResearch.WordTrace]
  refine ⟨124302889493111951146890967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165737185990815934862521289 124302889493111951146890967)
  ·
    refine ⟨186454334239667926720336451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124302889493111951146890967 186454334239667926720336451)
    ·
      refine ⟨279681501359501890080504677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186454334239667926720336451 279681501359501890080504677)
      ·
        refine ⟨52440281504906604390094627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279681501359501890080504677 52440281504906604390094627)
        ·
          refine ⟨78660422257359906585141941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52440281504906604390094627 78660422257359906585141941)
          ·
            refine ⟨7374414586627491242357057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78660422257359906585141941 7374414586627491242357057)
            ·
              refine ⟨5530810939970618431767793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7374414586627491242357057 5530810939970618431767793)
              ·
                refine ⟨4148108204977963823825845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5530810939970618431767793 4148108204977963823825845)
                ·
                  refine ⟨388885144216684108483673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4148108204977963823825845 388885144216684108483673)
                  ·
                    rfl

theorem cell23_6816160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 2, 5].length) (baseStart_6816160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816160 prefixEnd_6816160 := by exact prefixLift 6816160
  have htrace : WordTrace (prefixWord ++ tailWord_6816160) baseStart_6816160 baseEnd_6816160 := by
    simpa [prefixWord, tailWord_6816160, baseEnd_6816160] using wordTrace_append hprefix tailTrace_6816160
  have hstable : (prefixWord ++ tailWord_6816160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816160).length < 2 ^ (prefixWord ++ tailWord_6816160).sum := by decide
  have hdescent : baseEnd_6816160 < baseStart_6816160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816243 : List Nat := [1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 3]
def baseStart_6816243 : Nat := 118140960795 + 6816243 * 2 ^ 59
def prefixEnd_6816243 : Nat := 4983230072969 + 3 ^ 40 * 6816243 * 2
def baseEnd_6816243 : Nat := 3500008916844480151615175

theorem tailTrace_6816243 : CollatzResearch.WordTrace tailWord_6816243 prefixEnd_6816243 3500008916844480151615175 := by
  unfold tailWord_6816243
  simp only [CollatzResearch.WordTrace]
  refine ⟨248608806244923207469053383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165739204163282138312702255 248608806244923207469053383)
  ·
    refine ⟨372913209367384811203580075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248608806244923207469053383 372913209367384811203580075)
    ·
      refine ⟨559369814051077216805370113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372913209367384811203580075 559369814051077216805370113)
      ·
        refine ⟨419527360538307912604027585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559369814051077216805370113 419527360538307912604027585)
        ·
          refine ⟨314645520403730934453020689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419527360538307912604027585 314645520403730934453020689)
          ·
            refine ⟨235984140302798200839765517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314645520403730934453020689 235984140302798200839765517)
            ·
              refine ⟨88494052613549325314912069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235984140302798200839765517 88494052613549325314912069)
              ·
                refine ⟨16592634865040498496546013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88494052613549325314912069 16592634865040498496546013)
                ·
                  refine ⟨6222238074390186936204755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16592634865040498496546013 6222238074390186936204755)
                  ·
                    refine ⟨9333357111585280404307133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6222238074390186936204755 9333357111585280404307133)
                    ·
                      refine ⟨3500008916844480151615175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333357111585280404307133 3500008916844480151615175)
                      ·
                        rfl

theorem cell23_6816243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 3, 1, 3].length) (baseStart_6816243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816243 prefixEnd_6816243 := by exact prefixLift 6816243
  have htrace : WordTrace (prefixWord ++ tailWord_6816243) baseStart_6816243 baseEnd_6816243 := by
    simpa [prefixWord, tailWord_6816243, baseEnd_6816243] using wordTrace_append hprefix tailTrace_6816243
  have hstable : (prefixWord ++ tailWord_6816243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816243).length < 2 ^ (prefixWord ++ tailWord_6816243).sum := by decide
  have hdescent : baseEnd_6816243 < baseStart_6816243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816253 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_6816253 : Nat := 118140960795 + 6816253 * 2 ^ 59
def prefixEnd_6816253 : Nat := 4983230072969 + 3 ^ 40 * 6816253 * 2
def baseEnd_6816253 : Nat := 3500014051651025112490129

theorem tailTrace_6816253 : CollatzResearch.WordTrace tailWord_6816253 prefixEnd_6816253 3500014051651025112490129 := by
  unfold tailWord_6816253
  simp only [CollatzResearch.WordTrace]
  refine ⟨248609170974886979176917413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165739447316591319451278275 248609170974886979176917413)
  ·
    refine ⟨46614219557791308595672015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248609170974886979176917413 46614219557791308595672015)
    ·
      refine ⟨69921329336686962893508023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46614219557791308595672015 69921329336686962893508023)
      ·
        refine ⟨104881994005030444340262035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69921329336686962893508023 104881994005030444340262035)
        ·
          refine ⟨157322991007545666510393053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104881994005030444340262035 157322991007545666510393053)
          ·
            refine ⟨58996121627829624941397395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157322991007545666510393053 58996121627829624941397395)
            ·
              refine ⟨88494182441744437412096093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58996121627829624941397395 88494182441744437412096093)
              ·
                refine ⟨33185318415654164029536035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88494182441744437412096093 33185318415654164029536035)
                ·
                  refine ⟨49777977623481246044304053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33185318415654164029536035 49777977623481246044304053)
                  ·
                    refine ⟨4666685402201366816653505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49777977623481246044304053 4666685402201366816653505)
                    ·
                      refine ⟨3500014051651025112490129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666685402201366816653505 3500014051651025112490129)
                      ·
                        rfl

theorem cell23_6816253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_6816253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816253 prefixEnd_6816253 := by exact prefixLift 6816253
  have htrace : WordTrace (prefixWord ++ tailWord_6816253) baseStart_6816253 baseEnd_6816253 := by
    simpa [prefixWord, tailWord_6816253, baseEnd_6816253] using wordTrace_append hprefix tailTrace_6816253
  have hstable : (prefixWord ++ tailWord_6816253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816253).length < 2 ^ (prefixWord ++ tailWord_6816253).sum := by decide
  have hdescent : baseEnd_6816253 < baseStart_6816253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816270 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_6816270 : Nat := 118140960795 + 6816270 * 2 ^ 59
def prefixEnd_6816270 : Nat := 4983230072969 + 3 ^ 40 * 6816270 * 2
def baseEnd_6816270 : Nat := 3500022780822151545977551

theorem tailTrace_6816270 : CollatzResearch.WordTrace tailWord_6816270 prefixEnd_6816270 3500022780822151545977551 := by
  unfold tailWord_6816270
  simp only [CollatzResearch.WordTrace]
  refine ⟨31076223876978173885035783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165739860677216927386857509 31076223876978173885035783)
  ·
    refine ⟨46614335815467260827553675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31076223876978173885035783 46614335815467260827553675)
    ·
      refine ⟨69921503723200891241330513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46614335815467260827553675 69921503723200891241330513)
      ·
        refine ⟨52441127792400668430997885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69921503723200891241330513 52441127792400668430997885)
        ·
          refine ⟨19665422922150250661624207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52441127792400668430997885 19665422922150250661624207)
          ·
            refine ⟨29498134383225375992436311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19665422922150250661624207 29498134383225375992436311)
            ·
              refine ⟨44247201574838063988654467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29498134383225375992436311 44247201574838063988654467)
              ·
                refine ⟨66370802362257095982981701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44247201574838063988654467 66370802362257095982981701)
                ·
                  refine ⟨12444525442923205496809069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66370802362257095982981701 12444525442923205496809069)
                  ·
                    refine ⟨4666697041096202061303401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12444525442923205496809069 4666697041096202061303401)
                    ·
                      refine ⟨3500022780822151545977551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666697041096202061303401 3500022780822151545977551)
                      ·
                        rfl

theorem cell23_6816270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_6816270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816270 prefixEnd_6816270 := by exact prefixLift 6816270
  have htrace : WordTrace (prefixWord ++ tailWord_6816270) baseStart_6816270 baseEnd_6816270 := by
    simpa [prefixWord, tailWord_6816270, baseEnd_6816270] using wordTrace_append hprefix tailTrace_6816270
  have hstable : (prefixWord ++ tailWord_6816270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816270).length < 2 ^ (prefixWord ++ tailWord_6816270).sum := by decide
  have hdescent : baseEnd_6816270 < baseStart_6816270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816300 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 3, 2, 2]
def baseStart_6816300 : Nat := 118140960795 + 6816300 * 2 ^ 59
def prefixEnd_6816300 : Nat := 4983230072969 + 3 ^ 40 * 6816300 * 2
def baseEnd_6816300 : Nat := 3500038185241786428602413

theorem tailTrace_6816300 : CollatzResearch.WordTrace tailWord_6816300 prefixEnd_6816300 3500038185241786428602413 := by
  unfold tailWord_6816300
  simp only [CollatzResearch.WordTrace]
  refine ⟨124305442602858353101939177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165740590137144470802585569 124305442602858353101939177)
  ·
    refine ⟨93229081952143764826454383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124305442602858353101939177 93229081952143764826454383)
    ·
      refine ⟨139843622928215647239681575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93229081952143764826454383 139843622928215647239681575)
      ·
        refine ⟨209765434392323470859522363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139843622928215647239681575 209765434392323470859522363)
        ·
          refine ⟨314648151588485206289283545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209765434392323470859522363 314648151588485206289283545)
          ·
            refine ⟨235986113691363904716962659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314648151588485206289283545 235986113691363904716962659)
            ·
              refine ⟨353979170537045857075443989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235986113691363904716962659 353979170537045857075443989)
              ·
                refine ⟨16592773618924024550411437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 353979170537045857075443989 16592773618924024550411437)
                ·
                  refine ⟨6222290107096509206404289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16592773618924024550411437 6222290107096509206404289)
                  ·
                    refine ⟨4666717580322381904803217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6222290107096509206404289 4666717580322381904803217)
                    ·
                      refine ⟨3500038185241786428602413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666717580322381904803217 3500038185241786428602413)
                      ·
                        rfl

theorem cell23_6816300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 2, 2].length) (baseStart_6816300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816300 prefixEnd_6816300 := by exact prefixLift 6816300
  have htrace : WordTrace (prefixWord ++ tailWord_6816300) baseStart_6816300 baseEnd_6816300 := by
    simpa [prefixWord, tailWord_6816300, baseEnd_6816300] using wordTrace_append hprefix tailTrace_6816300
  have hstable : (prefixWord ++ tailWord_6816300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816300).length < 2 ^ (prefixWord ++ tailWord_6816300).sum := by decide
  have hdescent : baseEnd_6816300 < baseStart_6816300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816306 : List Nat := [3, 2, 1, 1, 2, 1, 4, 9]
def baseStart_6816306 : Nat := 118140960795 + 6816306 * 2 ^ 59
def prefixEnd_6816306 : Nat := 4983230072969 + 3 ^ 40 * 6816306 * 2
def baseEnd_6816306 : Nat := 129631158004656052041755

theorem tailTrace_6816306 : CollatzResearch.WordTrace tailWord_6816306 prefixEnd_6816306 129631158004656052041755 := by
  unfold tailWord_6816306
  simp only [CollatzResearch.WordTrace]
  refine ⟨62152776010923742307149193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165740736029129979485731181 62152776010923742307149193)
  ·
    refine ⟨46614582008192806730361895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62152776010923742307149193 46614582008192806730361895)
    ·
      refine ⟨69921873012289210095542843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46614582008192806730361895 69921873012289210095542843)
      ·
        refine ⟨104882809518433815143314265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69921873012289210095542843 104882809518433815143314265)
        ·
          refine ⟨78662107138825361357485699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104882809518433815143314265 78662107138825361357485699)
          ·
            refine ⟨117993160708238042036228549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78662107138825361357485699 117993160708238042036228549)
            ·
              refine ⟨22123717632794632881792853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117993160708238042036228549 22123717632794632881792853)
              ·
                refine ⟨129631158004656052041755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22123717632794632881792853 129631158004656052041755)
                ·
                  rfl

theorem cell23_6816306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 9].length) (baseStart_6816306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816306 prefixEnd_6816306 := by exact prefixLift 6816306
  have htrace : WordTrace (prefixWord ++ tailWord_6816306) baseStart_6816306 baseEnd_6816306 := by
    simpa [prefixWord, tailWord_6816306, baseEnd_6816306] using wordTrace_append hprefix tailTrace_6816306
  have hstable : (prefixWord ++ tailWord_6816306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816306).length < 2 ^ (prefixWord ++ tailWord_6816306).sum := by decide
  have hdescent : baseEnd_6816306 < baseStart_6816306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816310 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_6816310 : Nat := 118140960795 + 6816310 * 2 ^ 59
def prefixEnd_6816310 : Nat := 4983230072969 + 3 ^ 40 * 6816310 * 2
def baseEnd_6816310 : Nat := 1166681106682777129825789

theorem tailTrace_6816310 : CollatzResearch.WordTrace tailWord_6816310 prefixEnd_6816310 1166681106682777129825789 := by
  unfold tailWord_6816310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15538203120980029869483899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 165740833290453651941161589 15538203120980029869483899)
  ·
    refine ⟨23307304681470044804225849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15538203120980029869483899 23307304681470044804225849)
    ·
      refine ⟨17480478511102533603169387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23307304681470044804225849 17480478511102533603169387)
      ·
        refine ⟨26220717766653800404754081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17480478511102533603169387 26220717766653800404754081)
        ·
          refine ⟨19665538324990350303565561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26220717766653800404754081 19665538324990350303565561)
          ·
            refine ⟨14749153743742762727674171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19665538324990350303565561 14749153743742762727674171)
            ·
              refine ⟨22123730615614144091511257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14749153743742762727674171 22123730615614144091511257)
              ·
                refine ⟨16592797961710608068633443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22123730615614144091511257 16592797961710608068633443)
                ·
                  refine ⟨24889196942565912102950165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16592797961710608068633443 24889196942565912102950165)
                  ·
                    refine ⟨1166681106682777129825789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24889196942565912102950165 1166681106682777129825789)
                    ·
                      rfl

theorem cell23_6816310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_6816310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816310 prefixEnd_6816310 := by exact prefixLift 6816310
  have htrace : WordTrace (prefixWord ++ tailWord_6816310) baseStart_6816310 baseEnd_6816310 := by
    simpa [prefixWord, tailWord_6816310, baseEnd_6816310] using wordTrace_append hprefix tailTrace_6816310
  have hstable : (prefixWord ++ tailWord_6816310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816310).length < 2 ^ (prefixWord ++ tailWord_6816310).sum := by decide
  have hdescent : baseEnd_6816310 < baseStart_6816310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816313 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6816313 : Nat := 118140960795 + 6816313 * 2 ^ 59
def prefixEnd_6816313 : Nat := 4983230072969 + 3 ^ 40 * 6816313 * 2
def baseEnd_6816313 : Nat := 3500044860490294877739853

theorem tailTrace_6816313 : CollatzResearch.WordTrace tailWord_6816313 prefixEnd_6816313 3500044860490294877739853 := by
  unfold tailWord_6816313
  simp only [CollatzResearch.WordTrace]
  refine ⟨248611359354669609424101593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165740906236446406282734395 248611359354669609424101593)
  ·
    refine ⟨186458519516002207068076195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248611359354669609424101593 186458519516002207068076195)
    ·
      refine ⟨279687779274003310602114293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186458519516002207068076195 279687779274003310602114293)
      ·
        refine ⟨26220729306937810368948215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279687779274003310602114293 26220729306937810368948215)
        ·
          refine ⟨39331093960406715553422323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26220729306937810368948215 39331093960406715553422323)
          ·
            refine ⟨58996640940610073330133485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39331093960406715553422323 58996640940610073330133485)
            ·
              refine ⟨22123740352728777498800057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58996640940610073330133485 22123740352728777498800057)
              ·
                refine ⟨16592805264546583124100043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22123740352728777498800057 16592805264546583124100043)
                ·
                  refine ⟨24889207896819874686150065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16592805264546583124100043 24889207896819874686150065)
                  ·
                    refine ⟨18666905922614906014612549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24889207896819874686150065 18666905922614906014612549)
                    ·
                      refine ⟨3500044860490294877739853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18666905922614906014612549 3500044860490294877739853)
                      ·
                        rfl

theorem cell23_6816313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6816313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816313 prefixEnd_6816313 := by exact prefixLift 6816313
  have htrace : WordTrace (prefixWord ++ tailWord_6816313) baseStart_6816313 baseEnd_6816313 := by
    simpa [prefixWord, tailWord_6816313, baseEnd_6816313] using wordTrace_append hprefix tailTrace_6816313
  have hstable : (prefixWord ++ tailWord_6816313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816313).length < 2 ^ (prefixWord ++ tailWord_6816313).sum := by decide
  have hdescent : baseEnd_6816313 < baseStart_6816313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816317 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6816317 : Nat := 118140960795 + 6816317 * 2 ^ 59
def prefixEnd_6816317 : Nat := 4983230072969 + 3 ^ 40 * 6816317 * 2
def baseEnd_6816317 : Nat := 3500046914412912862089835

theorem tailTrace_6816317 : CollatzResearch.WordTrace tailWord_6816317 prefixEnd_6816317 3500046914412912862089835 := by
  unfold tailWord_6816317
  simp only [CollatzResearch.WordTrace]
  refine ⟨248611505246655118107247205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165741003497770078738164803 248611505246655118107247205)
  ·
    refine ⟨46614657233747834645108851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248611505246655118107247205 46614657233747834645108851)
    ·
      refine ⟨69921985850621751967663277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46614657233747834645108851 69921985850621751967663277)
      ·
        refine ⟨26220744693983156987873729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69921985850621751967663277 26220744693983156987873729)
        ·
          refine ⟨19665558520487367740905297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26220744693983156987873729 19665558520487367740905297)
          ·
            refine ⟨14749168890365525805678973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19665558520487367740905297 14749168890365525805678973)
            ·
              refine ⟨5530938333887072177129615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14749168890365525805678973 5530938333887072177129615)
              ·
                refine ⟨8296407500830608265694423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530938333887072177129615 8296407500830608265694423)
                ·
                  refine ⟨12444611251245912398541635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296407500830608265694423 12444611251245912398541635)
                  ·
                    refine ⟨18666916876868868597812453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12444611251245912398541635 18666916876868868597812453)
                    ·
                      refine ⟨3500046914412912862089835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18666916876868868597812453 3500046914412912862089835)
                      ·
                        rfl

theorem cell23_6816317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6816317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816317 prefixEnd_6816317 := by exact prefixLift 6816317
  have htrace : WordTrace (prefixWord ++ tailWord_6816317) baseStart_6816317 baseEnd_6816317 := by
    simpa [prefixWord, tailWord_6816317, baseEnd_6816317] using wordTrace_append hprefix tailTrace_6816317
  have hstable : (prefixWord ++ tailWord_6816317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816317).length < 2 ^ (prefixWord ++ tailWord_6816317).sum := by decide
  have hdescent : baseEnd_6816317 < baseStart_6816317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816346 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_6816346 : Nat := 118140960795 + 6816346 * 2 ^ 59
def prefixEnd_6816346 : Nat := 4983230072969 + 3 ^ 40 * 6816346 * 2
def baseEnd_6816346 : Nat := 3500061805351893248627201

theorem tailTrace_6816346 : CollatzResearch.WordTrace tailWord_6816346 prefixEnd_6816346 3500061805351893248627201 := by
  unfold tailWord_6816346
  simp only [CollatzResearch.WordTrace]
  refine ⟨62153140740887514015013223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165741708642366704040035261 62153140740887514015013223)
  ·
    refine ⟨93229711111331271022519835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62153140740887514015013223 93229711111331271022519835)
    ·
      refine ⟨139844566666996906533779753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93229711111331271022519835 139844566666996906533779753)
      ·
        refine ⟨104883425000247679900334815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139844566666996906533779753 104883425000247679900334815)
        ·
          refine ⟨157325137500371519850502223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104883425000247679900334815 157325137500371519850502223)
          ·
            refine ⟨235987706250557279775753335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157325137500371519850502223 235987706250557279775753335)
            ·
              refine ⟨353981559375835919663630003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235987706250557279775753335 353981559375835919663630003)
              ·
                refine ⟨530972339063753879495445005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353981559375835919663630003 530972339063753879495445005)
                ·
                  refine ⟨199114627148907704810791877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 530972339063753879495445005 199114627148907704810791877)
                  ·
                    refine ⟨37333992590420194652023477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199114627148907704810791877 37333992590420194652023477)
                    ·
                      refine ⟨3500061805351893248627201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37333992590420194652023477 3500061805351893248627201)
                      ·
                        rfl

theorem cell23_6816346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_6816346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816346 prefixEnd_6816346 := by exact prefixLift 6816346
  have htrace : WordTrace (prefixWord ++ tailWord_6816346) baseStart_6816346 baseEnd_6816346 := by
    simpa [prefixWord, tailWord_6816346, baseEnd_6816346] using wordTrace_append hprefix tailTrace_6816346
  have hstable : (prefixWord ++ tailWord_6816346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816346).length < 2 ^ (prefixWord ++ tailWord_6816346).sum := by decide
  have hdescent : baseEnd_6816346 < baseStart_6816346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816377 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 1, 3, 2]
def baseStart_6816377 : Nat := 118140960795 + 6816377 * 2 ^ 59
def prefixEnd_6816377 : Nat := 4983230072969 + 3 ^ 40 * 6816377 * 2
def baseEnd_6816377 : Nat := 3500077723252182627339559

theorem tailTrace_6816377 : CollatzResearch.WordTrace tailWord_6816377 prefixEnd_6816377 3500077723252182627339559 := by
  unfold tailWord_6816377
  simp only [CollatzResearch.WordTrace]
  refine ⟨248613693626437748354431385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165742462417625165569620923 248613693626437748354431385)
  ·
    refine ⟨186460270219828311265823539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248613693626437748354431385 186460270219828311265823539)
    ·
      refine ⟨279690405329742466898735309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186460270219828311265823539 279690405329742466898735309)
      ·
        refine ⟨104883901998653425087025741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279690405329742466898735309 104883901998653425087025741)
        ·
          refine ⟨39331463249495034407634653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104883901998653425087025741 39331463249495034407634653)
          ·
            refine ⟨14749298718560637902862995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39331463249495034407634653 14749298718560637902862995)
            ·
              refine ⟨22123948077840956854294493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14749298718560637902862995 22123948077840956854294493)
              ·
                refine ⟨8296480529190358820360435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22123948077840956854294493 8296480529190358820360435)
                ·
                  refine ⟨12444720793785538230540653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296480529190358820360435 12444720793785538230540653)
                  ·
                    refine ⟨4666770297669576836452745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12444720793785538230540653 4666770297669576836452745)
                    ·
                      refine ⟨3500077723252182627339559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666770297669576836452745 3500077723252182627339559)
                      ·
                        rfl

theorem cell23_6816377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_6816377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816377 prefixEnd_6816377 := by exact prefixLift 6816377
  have htrace : WordTrace (prefixWord ++ tailWord_6816377) baseStart_6816377 baseEnd_6816377 := by
    simpa [prefixWord, tailWord_6816377, baseEnd_6816377] using wordTrace_append hprefix tailTrace_6816377
  have hstable : (prefixWord ++ tailWord_6816377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816377).length < 2 ^ (prefixWord ++ tailWord_6816377).sum := by decide
  have hdescent : baseEnd_6816377 < baseStart_6816377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816413 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 7]
def baseStart_6816413 : Nat := 118140960795 + 6816413 * 2 ^ 59
def prefixEnd_6816413 : Nat := 4983230072969 + 3 ^ 40 * 6816413 * 2
def baseEnd_6816413 : Nat := 388899578728416054054377

theorem tailTrace_6816413 : CollatzResearch.WordTrace tailWord_6816413 prefixEnd_6816413 388899578728416054054377 := by
  unfold tailWord_6816413
  simp only [CollatzResearch.WordTrace]
  refine ⟨248615006654307326502741893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165743337769538217668494595 248615006654307326502741893)
  ·
    refine ⟨46615313747682623719264105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 248615006654307326502741893 46615313747682623719264105)
    ·
      refine ⟨34961485310761967789448079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46615313747682623719264105 34961485310761967789448079)
      ·
        refine ⟨52442227966142951684172119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34961485310761967789448079 52442227966142951684172119)
        ·
          refine ⟨78663341949214427526258179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52442227966142951684172119 78663341949214427526258179)
          ·
            refine ⟨117995012923821641289387269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78663341949214427526258179 117995012923821641289387269)
            ·
              refine ⟨22124064923216557741760113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117995012923821641289387269 22124064923216557741760113)
              ·
                refine ⟨16593048692412418306320085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22124064923216557741760113 16593048692412418306320085)
                ·
                  refine ⟨388899578728416054054377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16593048692412418306320085 388899578728416054054377)
                  ·
                    rfl

theorem cell23_6816413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_6816413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816413 prefixEnd_6816413 := by exact prefixLift 6816413
  have htrace : WordTrace (prefixWord ++ tailWord_6816413) baseStart_6816413 baseEnd_6816413 := by
    simpa [prefixWord, tailWord_6816413, baseEnd_6816413] using wordTrace_append hprefix tailTrace_6816413
  have hstable : (prefixWord ++ tailWord_6816413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816413).length < 2 ^ (prefixWord ++ tailWord_6816413).sum := by decide
  have hdescent : baseEnd_6816413 < baseStart_6816413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816447 : List Nat := [1, 1, 2, 2, 2, 5, 3, 2, 5]
def baseStart_6816447 : Nat := 118140960795 + 6816447 * 2 ^ 59
def prefixEnd_6816447 : Nat := 4983230072969 + 3 ^ 40 * 6816447 * 2
def baseEnd_6816447 : Nat := 388901518544221928162693

theorem tailTrace_6816447 : CollatzResearch.WordTrace tailWord_6816447 prefixEnd_6816447 388901518544221928162693 := by
  unfold tailWord_6816447
  simp only [CollatzResearch.WordTrace]
  refine ⟨248616246736184150309479595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165744164490789433539653063 248616246736184150309479595)
  ·
    refine ⟨372924370104276225464219393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248616246736184150309479595 372924370104276225464219393)
    ·
      refine ⟨279693277578207169098164545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372924370104276225464219393 279693277578207169098164545)
      ·
        refine ⟨209769958183655376823623409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279693277578207169098164545 209769958183655376823623409)
        ·
          refine ⟨157327468637741532617717557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209769958183655376823623409 157327468637741532617717557)
          ·
            refine ⟨14749450184788268682911021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157327468637741532617717557 14749450184788268682911021)
            ·
              refine ⟨5531043819295600756091633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14749450184788268682911021 5531043819295600756091633)
              ·
                refine ⟨4148282864471700567068725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5531043819295600756091633 4148282864471700567068725)
                ·
                  refine ⟨388901518544221928162693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4148282864471700567068725 388901518544221928162693)
                  ·
                    rfl

theorem cell23_6816447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 2, 5].length) (baseStart_6816447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816447 prefixEnd_6816447 := by exact prefixLift 6816447
  have htrace : WordTrace (prefixWord ++ tailWord_6816447) baseStart_6816447 baseEnd_6816447 := by
    simpa [prefixWord, tailWord_6816447, baseEnd_6816447] using wordTrace_append hprefix tailTrace_6816447
  have hstable : (prefixWord ++ tailWord_6816447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816447).length < 2 ^ (prefixWord ++ tailWord_6816447).sum := by decide
  have hdescent : baseEnd_6816447 < baseStart_6816447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816480 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 4, 4, 2]
def baseStart_6816480 : Nat := 118140960795 + 6816480 * 2 ^ 59
def prefixEnd_6816480 : Nat := 4983230072969 + 3 ^ 40 * 6816480 * 2
def baseEnd_6816480 : Nat := 3500130611759595724351585

theorem tailTrace_6816480 : CollatzResearch.WordTrace tailWord_6816480 prefixEnd_6816480 3500130611759595724351585 := by
  unfold tailWord_6816480
  simp only [CollatzResearch.WordTrace]
  refine ⟨124308725172532298472715447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165744966896709731296953929 124308725172532298472715447)
  ·
    refine ⟨186463087758798447709073171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124308725172532298472715447 186463087758798447709073171)
    ·
      refine ⟨279694631638197671563609757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186463087758798447709073171 279694631638197671563609757)
      ·
        refine ⟨104885486864324126836353659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279694631638197671563609757 104885486864324126836353659)
        ·
          refine ⟨157328230296486190254530489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104885486864324126836353659 157328230296486190254530489)
          ·
            refine ⟨117996172722364642690897867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157328230296486190254530489 117996172722364642690897867)
            ·
              refine ⟨176994259083546964036346801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117996172722364642690897867 176994259083546964036346801)
              ·
                refine ⟨132745694312660223027260101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176994259083546964036346801 132745694312660223027260101)
                ·
                  refine ⟨24889817683623791817611269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132745694312660223027260101 24889817683623791817611269)
                  ·
                    refine ⟨4666840815679460965802113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24889817683623791817611269 4666840815679460965802113)
                    ·
                      refine ⟨3500130611759595724351585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666840815679460965802113 3500130611759595724351585)
                      ·
                        rfl

theorem cell23_6816480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_6816480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816480 prefixEnd_6816480 := by exact prefixLift 6816480
  have htrace : WordTrace (prefixWord ++ tailWord_6816480) baseStart_6816480 baseEnd_6816480 := by
    simpa [prefixWord, tailWord_6816480, baseEnd_6816480] using wordTrace_append hprefix tailTrace_6816480
  have hstable : (prefixWord ++ tailWord_6816480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816480).length < 2 ^ (prefixWord ++ tailWord_6816480).sum := by decide
  have hdescent : baseEnd_6816480 < baseStart_6816480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816514 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_6816514 : Nat := 118140960795 + 6816514 * 2 ^ 59
def prefixEnd_6816514 : Nat := 4983230072969 + 3 ^ 40 * 6816514 * 2
def baseEnd_6816514 : Nat := 3500148070101848591326429

theorem tailTrace_6816514 : CollatzResearch.WordTrace tailWord_6816514 prefixEnd_6816514 3500148070101848591326429 := by
  unfold tailWord_6816514
  simp only [CollatzResearch.WordTrace]
  refine ⟨62154672606735355188042149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165745793617960947168112397 62154672606735355188042149)
  ·
    refine ⟨11654001113762879097757903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62154672606735355188042149 11654001113762879097757903)
    ·
      refine ⟨17481001670644318646636855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654001113762879097757903 17481001670644318646636855)
      ·
        refine ⟨26221502505966477969955283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17481001670644318646636855 26221502505966477969955283)
        ·
          refine ⟨39332253758949716954932925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26221502505966477969955283 39332253758949716954932925)
          ·
            refine ⟨14749595159606143858099847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39332253758949716954932925 14749595159606143858099847)
            ·
              refine ⟨22124392739409215787149771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14749595159606143858099847 22124392739409215787149771)
              ·
                refine ⟨33186589109113823680724657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22124392739409215787149771 33186589109113823680724657)
                ·
                  refine ⟨24889941831835367760543493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33186589109113823680724657 24889941831835367760543493)
                  ·
                    refine ⟨4666864093469131455101905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24889941831835367760543493 4666864093469131455101905)
                    ·
                      refine ⟨3500148070101848591326429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4666864093469131455101905 3500148070101848591326429)
                      ·
                        rfl

theorem cell23_6816514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_6816514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816514 prefixEnd_6816514 := by exact prefixLift 6816514
  have htrace : WordTrace (prefixWord ++ tailWord_6816514) baseStart_6816514 baseEnd_6816514 := by
    simpa [prefixWord, tailWord_6816514, baseEnd_6816514] using wordTrace_append hprefix tailTrace_6816514
  have hstable : (prefixWord ++ tailWord_6816514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816514).length < 2 ^ (prefixWord ++ tailWord_6816514).sum := by decide
  have hdescent : baseEnd_6816514 < baseStart_6816514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816520 : List Nat := [2, 1, 3, 2, 2, 2, 2, 3, 6]
def baseStart_6816520 : Nat := 118140960795 + 6816520 * 2 ^ 59
def prefixEnd_6816520 : Nat := 4983230072969 + 3 ^ 40 * 6816520 * 2
def baseEnd_6816520 : Nat := 388905683442863951983489

theorem tailTrace_6816520 : CollatzResearch.WordTrace tailWord_6816520 prefixEnd_6816520 388905683442863951983489 := by
  unfold tailWord_6816520
  simp only [CollatzResearch.WordTrace]
  refine ⟨124309454632459841888443507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165745939509946455851258009 124309454632459841888443507)
  ·
    refine ⟨186464181948689762832665261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124309454632459841888443507 186464181948689762832665261)
    ·
      refine ⟨69924068230758661062249473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186464181948689762832665261 69924068230758661062249473)
      ·
        refine ⟨52443051173068995796687105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69924068230758661062249473 52443051173068995796687105)
        ·
          refine ⟨39332288379801746847515329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52443051173068995796687105 39332288379801746847515329)
          ·
            refine ⟨29499216284851310135636497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39332288379801746847515329 29499216284851310135636497)
            ·
              refine ⟨22124412213638482601727373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29499216284851310135636497 22124412213638482601727373)
              ·
                refine ⟨8296654580114430975647765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22124412213638482601727373 8296654580114430975647765)
                ·
                  refine ⟨388905683442863951983489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8296654580114430975647765 388905683442863951983489)
                  ·
                    rfl

theorem cell23_6816520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 6].length) (baseStart_6816520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816520 prefixEnd_6816520 := by exact prefixLift 6816520
  have htrace : WordTrace (prefixWord ++ tailWord_6816520) baseStart_6816520 baseEnd_6816520 := by
    simpa [prefixWord, tailWord_6816520, baseEnd_6816520] using wordTrace_append hprefix tailTrace_6816520
  have hstable : (prefixWord ++ tailWord_6816520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816520).length < 2 ^ (prefixWord ++ tailWord_6816520).sum := by decide
  have hdescent : baseEnd_6816520 < baseStart_6816520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816590 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_6816590 : Nat := 118140960795 + 6816590 * 2 ^ 59
def prefixEnd_6816590 : Nat := 4983230072969 + 3 ^ 40 * 6816590 * 2
def baseEnd_6816590 : Nat := 3500187094631590293976079

theorem tailTrace_6816590 : CollatzResearch.WordTrace tailWord_6816590 prefixEnd_6816590 3500187094631590293976079 := by
  unfold tailWord_6816590
  simp only [CollatzResearch.WordTrace]
  refine ⟨31077682796833260716491903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165747641583110723821290149 31077682796833260716491903)
  ·
    refine ⟨46616524195249891074737855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31077682796833260716491903 46616524195249891074737855)
    ·
      refine ⟨69924786292874836612106783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46616524195249891074737855 69924786292874836612106783)
      ·
        refine ⟨104887179439312254918160175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69924786292874836612106783 104887179439312254918160175)
        ·
          refine ⟨157330769158968382377240263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104887179439312254918160175 157330769158968382377240263)
          ·
            refine ⟨235996153738452573565860395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157330769158968382377240263 235996153738452573565860395)
            ·
              refine ⟨353994230607678860348790593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235996153738452573565860395 353994230607678860348790593)
              ·
                refine ⟨265495672955759145261592945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 353994230607678860348790593 265495672955759145261592945)
                ·
                  refine ⟨199121754716819358946194709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 265495672955759145261592945 199121754716819358946194709)
                  ·
                    refine ⟨9333832252350907450602877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 199121754716819358946194709 9333832252350907450602877)
                    ·
                      refine ⟨3500187094631590293976079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333832252350907450602877 3500187094631590293976079)
                      ·
                        rfl

theorem cell23_6816590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_6816590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816590 prefixEnd_6816590 := by exact prefixLift 6816590
  have htrace : WordTrace (prefixWord ++ tailWord_6816590) baseStart_6816590 baseEnd_6816590 := by
    simpa [prefixWord, tailWord_6816590, baseEnd_6816590] using wordTrace_append hprefix tailTrace_6816590
  have hstable : (prefixWord ++ tailWord_6816590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816590).length < 2 ^ (prefixWord ++ tailWord_6816590).sum := by decide
  have hdescent : baseEnd_6816590 < baseStart_6816590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816600 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_6816600 : Nat := 118140960795 + 6816600 * 2 ^ 59
def prefixEnd_6816600 : Nat := 4983230072969 + 3 ^ 40 * 6816600 * 2
def baseEnd_6816600 : Nat := 3500192229438135254851033

theorem tailTrace_6816600 : CollatzResearch.WordTrace tailWord_6816600 prefixEnd_6816600 3500192229438135254851033 := by
  unfold tailWord_6816600
  simp only [CollatzResearch.WordTrace]
  refine ⟨124310913552314928719899627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165747884736419904959866169 124310913552314928719899627)
  ·
    refine ⟨186466370328472393079849441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124310913552314928719899627 186466370328472393079849441)
    ·
      refine ⟨139849777746354294809887081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186466370328472393079849441 139849777746354294809887081)
      ·
        refine ⟨104887333309765721107415311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139849777746354294809887081 104887333309765721107415311)
        ·
          refine ⟨157330999964648581661122967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104887333309765721107415311 157330999964648581661122967)
          ·
            refine ⟨235996499946972872491684451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157330999964648581661122967 235996499946972872491684451)
            ·
              refine ⟨353994749920459308737526677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235996499946972872491684451 353994749920459308737526677)
              ·
                refine ⟨16593503902521530097071563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 353994749920459308737526677 16593503902521530097071563)
                ·
                  refine ⟨24890255853782295145607345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16593503902521530097071563 24890255853782295145607345)
                  ·
                    refine ⟨18667691890336721359205509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24890255853782295145607345 18667691890336721359205509)
                    ·
                      refine ⟨3500192229438135254851033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18667691890336721359205509 3500192229438135254851033)
                      ·
                        rfl

theorem cell23_6816600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_6816600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816600 prefixEnd_6816600 := by exact prefixLift 6816600
  have htrace : WordTrace (prefixWord ++ tailWord_6816600) baseStart_6816600 baseEnd_6816600 := by
    simpa [prefixWord, tailWord_6816600, baseEnd_6816600] using wordTrace_append hprefix tailTrace_6816600
  have hstable : (prefixWord ++ tailWord_6816600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816600).length < 2 ^ (prefixWord ++ tailWord_6816600).sum := by decide
  have hdescent : baseEnd_6816600 < baseStart_6816600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_6816603 : Nat := 118140960795 + 6816603 * 2 ^ 59
def prefixEnd_6816603 : Nat := 4983230072969 + 3 ^ 40 * 6816603 * 2
def baseEnd_6816603 : Nat := 3500193769880098743113519

theorem tailTrace_6816603 : CollatzResearch.WordTrace tailWord_6816603 prefixEnd_6816603 3500193769880098743113519 := by
  unfold tailWord_6816603
  simp only [CollatzResearch.WordTrace]
  refine ⟨248621936523618988952158463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165747957682412659301438975 248621936523618988952158463)
  ·
    refine ⟨372932904785428483428237695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248621936523618988952158463 372932904785428483428237695)
    ·
      refine ⟨559399357178142725142356543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372932904785428483428237695 559399357178142725142356543)
      ·
        refine ⟨839099035767214087713534815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559399357178142725142356543 839099035767214087713534815)
        ·
          refine ⟨1258648553650821131570302223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839099035767214087713534815 1258648553650821131570302223)
          ·
            refine ⟨1887972830476231697355453335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258648553650821131570302223 1887972830476231697355453335)
            ·
              refine ⟨2831959245714347546033180003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1887972830476231697355453335 2831959245714347546033180003)
              ·
                refine ⟨4247938868571521319049770005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2831959245714347546033180003 4247938868571521319049770005)
                ·
                  refine ⟨199122134464290061830457969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4247938868571521319049770005 199122134464290061830457969)
                  ·
                    refine ⟨149341600848217546372843477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 199122134464290061830457969 149341600848217546372843477)
                    ·
                      refine ⟨3500193769880098743113519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149341600848217546372843477 3500193769880098743113519)
                      ·
                        rfl

theorem cell23_6816603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_6816603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816603 prefixEnd_6816603 := by exact prefixLift 6816603
  have htrace : WordTrace (prefixWord ++ tailWord_6816603) baseStart_6816603 baseEnd_6816603 := by
    simpa [prefixWord, tailWord_6816603, baseEnd_6816603] using wordTrace_append hprefix tailTrace_6816603
  have hstable : (prefixWord ++ tailWord_6816603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816603).length < 2 ^ (prefixWord ++ tailWord_6816603).sum := by decide
  have hdescent : baseEnd_6816603 < baseStart_6816603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816604 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6816604 : Nat := 118140960795 + 6816604 * 2 ^ 59
def prefixEnd_6816604 : Nat := 4983230072969 + 3 ^ 40 * 6816604 * 2
def baseEnd_6816604 : Nat := 3500194283360753239201015

theorem tailTrace_6816604 : CollatzResearch.WordTrace tailWord_6816604 prefixEnd_6816604 3500194283360753239201015 := by
  unfold tailWord_6816604
  simp only [CollatzResearch.WordTrace]
  refine ⟨124310986498307683061472433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165747981997743577415296577 124310986498307683061472433)
  ·
    refine ⟨93233239873730762296104325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124310986498307683061472433 93233239873730762296104325)
    ·
      refine ⟨17481232476324517930519561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93233239873730762296104325 17481232476324517930519561)
      ·
        refine ⟨13110924357243388447889671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17481232476324517930519561 13110924357243388447889671)
        ·
          refine ⟨19666386535865082671834507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13110924357243388447889671 19666386535865082671834507)
          ·
            refine ⟨29499579803797624007751761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19666386535865082671834507 29499579803797624007751761)
            ·
              refine ⟨22124684852848218005813821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29499579803797624007751761 22124684852848218005813821)
              ·
                refine ⟨8296756819818081752180183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22124684852848218005813821 8296756819818081752180183)
                ·
                  refine ⟨12445135229727122628270275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296756819818081752180183 12445135229727122628270275)
                  ·
                    refine ⟨18667702844590683942405413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12445135229727122628270275 18667702844590683942405413)
                    ·
                      refine ⟨3500194283360753239201015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18667702844590683942405413 3500194283360753239201015)
                      ·
                        rfl

theorem cell23_6816604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6816604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816604 prefixEnd_6816604 := by exact prefixLift 6816604
  have htrace : WordTrace (prefixWord ++ tailWord_6816604) baseStart_6816604 baseEnd_6816604 := by
    simpa [prefixWord, tailWord_6816604, baseEnd_6816604] using wordTrace_append hprefix tailTrace_6816604
  have hstable : (prefixWord ++ tailWord_6816604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816604).length < 2 ^ (prefixWord ++ tailWord_6816604).sum := by decide
  have hdescent : baseEnd_6816604 < baseStart_6816604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816607 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 3]
def baseStart_6816607 : Nat := 118140960795 + 6816607 * 2 ^ 59
def prefixEnd_6816607 : Nat := 4983230072969 + 3 ^ 40 * 6816607 * 2
def baseEnd_6816607 : Nat := 3500195823802716727463501

theorem tailTrace_6816607 : CollatzResearch.WordTrace tailWord_6816607 prefixEnd_6816607 3500195823802716727463501 := by
  unfold tailWord_6816607
  simp only [CollatzResearch.WordTrace]
  refine ⟨248622082415604497635304075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165748054943736331756869383 248622082415604497635304075)
  ·
    refine ⟨372933123623406746452956113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248622082415604497635304075 372933123623406746452956113)
    ·
      refine ⟨279699842717555059839717085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372933123623406746452956113 279699842717555059839717085)
      ·
        refine ⟨104887441019083147439893907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279699842717555059839717085 104887441019083147439893907)
        ·
          refine ⟨157331161528624721159840861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104887441019083147439893907 157331161528624721159840861)
          ·
            refine ⟨58999185573234270434940323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157331161528624721159840861 58999185573234270434940323)
            ·
              refine ⟨88498778359851405652410485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58999185573234270434940323 88498778359851405652410485)
              ·
                refine ⟨8296760471236069279913483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88498778359851405652410485 8296760471236069279913483)
                ·
                  refine ⟨12445140706854103919870225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296760471236069279913483 12445140706854103919870225)
                  ·
                    refine ⟨9333855530140577939902669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12445140706854103919870225 9333855530140577939902669)
                    ·
                      refine ⟨3500195823802716727463501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333855530140577939902669 3500195823802716727463501)
                      ·
                        rfl

theorem cell23_6816607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 2, 3].length) (baseStart_6816607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816607 prefixEnd_6816607 := by exact prefixLift 6816607
  have htrace : WordTrace (prefixWord ++ tailWord_6816607) baseStart_6816607 baseEnd_6816607 := by
    simpa [prefixWord, tailWord_6816607, baseEnd_6816607] using wordTrace_append hprefix tailTrace_6816607
  have hstable : (prefixWord ++ tailWord_6816607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816607).length < 2 ^ (prefixWord ++ tailWord_6816607).sum := by decide
  have hdescent : baseEnd_6816607 < baseStart_6816607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816638 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6816638 : Nat := 118140960795 + 6816638 * 2 ^ 59
def prefixEnd_6816638 : Nat := 4983230072969 + 3 ^ 40 * 6816638 * 2
def baseEnd_6816638 : Nat := 3500211741703006106175859

theorem tailTrace_6816638 : CollatzResearch.WordTrace tailWord_6816638 prefixEnd_6816638 3500211741703006106175859 := by
  unfold tailWord_6816638
  simp only [CollatzResearch.WordTrace]
  refine ⟨31077901634811523741210321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165748808718994793286455045 31077901634811523741210321)
  ·
    refine ⟨23308426226108642805907741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31077901634811523741210321 23308426226108642805907741)
    ·
      refine ⟨8740659834790741052215403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23308426226108642805907741 8740659834790741052215403)
      ·
        refine ⟨13110989752186111578323105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8740659834790741052215403 13110989752186111578323105)
        ·
          refine ⟨9833242314139583683742329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13110989752186111578323105 9833242314139583683742329)
          ·
            refine ⟨7374931735604687762806747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9833242314139583683742329 7374931735604687762806747)
            ·
              refine ⟨11062397603407031644210121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374931735604687762806747 11062397603407031644210121)
              ·
                refine ⟨8296798202555273733157591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11062397603407031644210121 8296798202555273733157591)
                ·
                  refine ⟨12445197303832910599736387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296798202555273733157591 12445197303832910599736387)
                  ·
                    refine ⟨18667795955749365899604581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12445197303832910599736387 18667795955749365899604581)
                    ·
                      refine ⟨3500211741703006106175859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18667795955749365899604581 3500211741703006106175859)
                      ·
                        rfl

theorem cell23_6816638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6816638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816638 prefixEnd_6816638 := by exact prefixLift 6816638
  have htrace : WordTrace (prefixWord ++ tailWord_6816638) baseStart_6816638 baseEnd_6816638 := by
    simpa [prefixWord, tailWord_6816638, baseEnd_6816638] using wordTrace_append hprefix tailTrace_6816638
  have hstable : (prefixWord ++ tailWord_6816638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816638).length < 2 ^ (prefixWord ++ tailWord_6816638).sum := by decide
  have hdescent : baseEnd_6816638 < baseStart_6816638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816658 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_6816658 : Nat := 118140960795 + 6816658 * 2 ^ 59
def prefixEnd_6816658 : Nat := 4983230072969 + 3 ^ 40 * 6816658 * 2
def baseEnd_6816658 : Nat := 3500222011316096027925767

theorem tailTrace_6816658 : CollatzResearch.WordTrace tailWord_6816658 prefixEnd_6816658 3500222011316096027925767 := by
  unfold tailWord_6816658
  simp only [CollatzResearch.WordTrace]
  refine ⟨62155985634604933336352657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165749295025613155563607085 62155985634604933336352657)
  ·
    refine ⟨46616989225953700002264493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62155985634604933336352657 46616989225953700002264493)
    ·
      refine ⟨17481370959732637500849185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46616989225953700002264493 17481370959732637500849185)
      ·
        refine ⟨13111028219799478125636889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17481370959732637500849185 13111028219799478125636889)
        ·
          refine ⟨9833271164849608594227667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13111028219799478125636889 9833271164849608594227667)
          ·
            refine ⟨14749906747274412891341501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9833271164849608594227667 14749906747274412891341501)
            ·
              refine ⟨5531215030227904834253063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14749906747274412891341501 5531215030227904834253063)
              ·
                refine ⟨8296822545341857251379595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531215030227904834253063 8296822545341857251379595)
                ·
                  refine ⟨12445233818012785877069393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8296822545341857251379595 12445233818012785877069393)
                  ·
                    refine ⟨9333925363509589407802045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12445233818012785877069393 9333925363509589407802045)
                    ·
                      refine ⟨3500222011316096027925767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333925363509589407802045 3500222011316096027925767)
                      ·
                        rfl

theorem cell23_6816658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_6816658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816658 prefixEnd_6816658 := by exact prefixLift 6816658
  have htrace : WordTrace (prefixWord ++ tailWord_6816658) baseStart_6816658 baseEnd_6816658 := by
    simpa [prefixWord, tailWord_6816658, baseEnd_6816658] using wordTrace_append hprefix tailTrace_6816658
  have hstable : (prefixWord ++ tailWord_6816658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816658).length < 2 ^ (prefixWord ++ tailWord_6816658).sum := by decide
  have hdescent : baseEnd_6816658 < baseStart_6816658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816671 : List Nat := [1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 3]
def baseStart_6816671 : Nat := 118140960795 + 6816671 * 2 ^ 59
def prefixEnd_6816671 : Nat := 4983230072969 + 3 ^ 40 * 6816671 * 2
def baseEnd_6816671 : Nat := 3500228686564604477063207

theorem tailTrace_6816671 : CollatzResearch.WordTrace tailWord_6816671 prefixEnd_6816671 3500228686564604477063207 := by
  unfold tailWord_6816671
  simp only [CollatzResearch.WordTrace]
  refine ⟨248624416687372636565633867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165749611124915091043755911 248624416687372636565633867)
  ·
    refine ⟨372936625031058954848450801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248624416687372636565633867 372936625031058954848450801)
    ·
      refine ⟨279702468773294216136338101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 372936625031058954848450801 279702468773294216136338101)
      ·
        refine ⟨26222106447496332762781697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279702468773294216136338101 26222106447496332762781697)
        ·
          refine ⟨19666579835622249572086273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26222106447496332762781697 19666579835622249572086273)
          ·
            refine ⟨14749934876716687179064705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19666579835622249572086273 14749934876716687179064705)
            ·
              refine ⟨11062451157537515384298529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14749934876716687179064705 11062451157537515384298529)
              ·
                refine ⟨8296838368153136538223897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11062451157537515384298529 8296838368153136538223897)
                ·
                  refine ⟨6222628776114852403667923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8296838368153136538223897 6222628776114852403667923)
                  ·
                    refine ⟨9333943164172278605501885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6222628776114852403667923 9333943164172278605501885)
                    ·
                      refine ⟨3500228686564604477063207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9333943164172278605501885 3500228686564604477063207)
                      ·
                        rfl

theorem cell23_6816671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_6816671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816671 prefixEnd_6816671 := by exact prefixLift 6816671
  have htrace : WordTrace (prefixWord ++ tailWord_6816671) baseStart_6816671 baseEnd_6816671 := by
    simpa [prefixWord, tailWord_6816671, baseEnd_6816671] using wordTrace_append hprefix tailTrace_6816671
  have hstable : (prefixWord ++ tailWord_6816671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816671).length < 2 ^ (prefixWord ++ tailWord_6816671).sum := by decide
  have hdescent : baseEnd_6816671 < baseStart_6816671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816728 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 2, 2, 2]
def baseStart_6816728 : Nat := 118140960795 + 6816728 * 2 ^ 59
def prefixEnd_6816728 : Nat := 4983230072969 + 3 ^ 40 * 6816728 * 2
def baseEnd_6816728 : Nat := 3500257954961910754050445

theorem tailTrace_6816728 : CollatzResearch.WordTrace tailWord_6816728 prefixEnd_6816728 3500257954961910754050445 := by
  unfold tailWord_6816728
  simp only [CollatzResearch.WordTrace]
  refine ⟨124313247824083067650229419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165750997098777423533639225 124313247824083067650229419)
  ·
    refine ⟨186469871736124601475344129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124313247824083067650229419 186469871736124601475344129)
    ·
      refine ⟨139852403802093451106508097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186469871736124601475344129 139852403802093451106508097)
      ·
        refine ⟨104889302851570088329881073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139852403802093451106508097 104889302851570088329881073)
        ·
          refine ⟨78666977138677566247410805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104889302851570088329881073 78666977138677566247410805)
          ·
            refine ⟨7375029106751021835694763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78666977138677566247410805 7375029106751021835694763)
            ·
              refine ⟨11062543660126532753542145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7375029106751021835694763 11062543660126532753542145)
              ·
                refine ⟨8296907745094899565156609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11062543660126532753542145 8296907745094899565156609)
                ·
                  refine ⟨6222680808821174673867457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8296907745094899565156609 6222680808821174673867457)
                  ·
                    refine ⟨4667010606615881005400593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6222680808821174673867457 4667010606615881005400593)
                    ·
                      refine ⟨3500257954961910754050445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667010606615881005400593 3500257954961910754050445)
                      ·
                        rfl

theorem cell23_6816728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_6816728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816728 prefixEnd_6816728 := by exact prefixLift 6816728
  have htrace : WordTrace (prefixWord ++ tailWord_6816728) baseStart_6816728 baseEnd_6816728 := by
    simpa [prefixWord, tailWord_6816728, baseEnd_6816728] using wordTrace_append hprefix tailTrace_6816728
  have hstable : (prefixWord ++ tailWord_6816728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816728).length < 2 ^ (prefixWord ++ tailWord_6816728).sum := by decide
  have hdescent : baseEnd_6816728 < baseStart_6816728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816760 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 10]
def baseStart_6816760 : Nat := 118140960795 + 6816760 * 2 ^ 59
def prefixEnd_6816760 : Nat := 4983230072969 + 3 ^ 40 * 6816760 * 2
def baseEnd_6816760 : Nat := 1166758128780951542950099

theorem tailTrace_6816760 : CollatzResearch.WordTrace tailWord_6816760 prefixEnd_6816760 1166758128780951542950099 := by
  unfold tailWord_6816760
  simp only [CollatzResearch.WordTrace]
  refine ⟨124313831392025102382811867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165751775189366803177082489 124313831392025102382811867)
  ·
    refine ⟨186470747088037653574217801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124313831392025102382811867 186470747088037653574217801)
    ·
      refine ⟨139853060316028240180663351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186470747088037653574217801 139853060316028240180663351)
      ·
        refine ⟨209779590474042360270995027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139853060316028240180663351 209779590474042360270995027)
        ·
          refine ⟨314669385711063540406492541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209779590474042360270995027 314669385711063540406492541)
          ·
            refine ⟨118001019641648827652434703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314669385711063540406492541 118001019641648827652434703)
            ·
              refine ⟨177001529462473241478652055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118001019641648827652434703 177001529462473241478652055)
              ·
                refine ⟨265502294193709862217978083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177001529462473241478652055 265502294193709862217978083)
                ·
                  refine ⟨398253441290564793326967125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265502294193709862217978083 398253441290564793326967125)
                  ·
                    refine ⟨1166758128780951542950099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 398253441290564793326967125 1166758128780951542950099)
                    ·
                      rfl

theorem cell23_6816760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_6816760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816760 prefixEnd_6816760 := by exact prefixLift 6816760
  have htrace : WordTrace (prefixWord ++ tailWord_6816760) baseStart_6816760 baseEnd_6816760 := by
    simpa [prefixWord, tailWord_6816760, baseEnd_6816760] using wordTrace_append hprefix tailTrace_6816760
  have hstable : (prefixWord ++ tailWord_6816760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816760).length < 2 ^ (prefixWord ++ tailWord_6816760).sum := by decide
  have hdescent : baseEnd_6816760 < baseStart_6816760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816777 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 5, 4]
def baseStart_6816777 : Nat := 118140960795 + 6816777 * 2 ^ 59
def prefixEnd_6816777 : Nat := 4983230072969 + 3 ^ 40 * 6816777 * 2
def baseEnd_6816777 : Nat := 1166761038504660354112573

theorem tailTrace_6816777 : CollatzResearch.WordTrace tailWord_6816777 prefixEnd_6816777 1166761038504660354112573 := by
  unfold tailWord_6816777
  simp only [CollatzResearch.WordTrace]
  refine ⟨248628282824988616668992585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165752188549992411112661723 248628282824988616668992585)
  ·
    refine ⟨186471212118741462501744439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248628282824988616668992585 186471212118741462501744439)
    ·
      refine ⟨279706818178112193752616659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186471212118741462501744439 279706818178112193752616659)
      ·
        refine ⟨419560227267168290628924989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279706818178112193752616659 419560227267168290628924989)
        ·
          refine ⟨157335085225188108985846871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419560227267168290628924989 157335085225188108985846871)
          ·
            refine ⟨236002627837782163478770307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157335085225188108985846871 236002627837782163478770307)
            ·
              refine ⟨354003941756673245218155461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236002627837782163478770307 354003941756673245218155461)
              ·
                refine ⟨66375739079376233478404149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354003941756673245218155461 66375739079376233478404149)
                ·
                  refine ⟨6222725538691521888600389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66375739079376233478404149 6222725538691521888600389)
                  ·
                    refine ⟨1166761038504660354112573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6222725538691521888600389 1166761038504660354112573)
                    ·
                      rfl

theorem cell23_6816777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_6816777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816777 prefixEnd_6816777 := by exact prefixLift 6816777
  have htrace : WordTrace (prefixWord ++ tailWord_6816777) baseStart_6816777 baseEnd_6816777 := by
    simpa [prefixWord, tailWord_6816777, baseEnd_6816777] using wordTrace_append hprefix tailTrace_6816777
  have hstable : (prefixWord ++ tailWord_6816777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816777).length < 2 ^ (prefixWord ++ tailWord_6816777).sum := by decide
  have hdescent : baseEnd_6816777 < baseStart_6816777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816838 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6816838 : Nat := 118140960795 + 6816838 * 2 ^ 59
def prefixEnd_6816838 : Nat := 4983230072969 + 3 ^ 40 * 6816838 * 2
def baseEnd_6816838 : Nat := 3500314437833905323674939

theorem tailTrace_6816838 : CollatzResearch.WordTrace tailWord_6816838 prefixEnd_6816838 3500314437833905323674939 := by
  unfold tailWord_6816838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7769703364930238252717599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 165753671785178416057975445 7769703364930238252717599)
  ·
    refine ⟨11654555047395357379076399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7769703364930238252717599 11654555047395357379076399)
    ·
      refine ⟨17481832571093036068614599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654555047395357379076399 17481832571093036068614599)
      ·
        refine ⟨26222748856639554102921899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17481832571093036068614599 26222748856639554102921899)
        ·
          refine ⟨39334123284959331154382849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26222748856639554102921899 39334123284959331154382849)
          ·
            refine ⟨29500592463719498365787137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39334123284959331154382849 29500592463719498365787137)
            ·
              refine ⟨22125444347789623774340353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29500592463719498365787137 22125444347789623774340353)
              ·
                refine ⟨16594083260842217830755265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22125444347789623774340353 16594083260842217830755265)
                ·
                  refine ⟨12445562445631663373066449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16594083260842217830755265 12445562445631663373066449)
                  ·
                    refine ⟨9334171834223747529799837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12445562445631663373066449 9334171834223747529799837)
                    ·
                      refine ⟨3500314437833905323674939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9334171834223747529799837 3500314437833905323674939)
                      ·
                        rfl

theorem cell23_6816838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6816838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816838 prefixEnd_6816838 := by exact prefixLift 6816838
  have htrace : WordTrace (prefixWord ++ tailWord_6816838) baseStart_6816838 baseEnd_6816838 := by
    simpa [prefixWord, tailWord_6816838, baseEnd_6816838] using wordTrace_append hprefix tailTrace_6816838
  have hstable : (prefixWord ++ tailWord_6816838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816838).length < 2 ^ (prefixWord ++ tailWord_6816838).sum := by decide
  have hdescent : baseEnd_6816838 < baseStart_6816838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816844 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 3, 5, 2]
def baseStart_6816844 : Nat := 118140960795 + 6816844 * 2 ^ 59
def prefixEnd_6816844 : Nat := 4983230072969 + 3 ^ 40 * 6816844 * 2
def baseEnd_6816844 : Nat := 3500317518717832300199911

theorem tailTrace_6816844 : CollatzResearch.WordTrace tailWord_6816844 prefixEnd_6816844 3500317518717832300199911 := by
  unfold tailWord_6816844
  simp only [CollatzResearch.WordTrace]
  refine ⟨124315363257872943555840793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165753817677163924741121057 124315363257872943555840793)
  ·
    refine ⟨93236522443404707666880595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124315363257872943555840793 93236522443404707666880595)
    ·
      refine ⟨139854783665107061500320893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93236522443404707666880595 139854783665107061500320893)
      ·
        refine ⟨52445543874415148062620335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139854783665107061500320893 52445543874415148062620335)
        ·
          refine ⟨78668315811622722093930503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52445543874415148062620335 78668315811622722093930503)
          ·
            refine ⟨118002473717434083140895755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78668315811622722093930503 118002473717434083140895755)
            ·
              refine ⟨177003710576151124711343633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118002473717434083140895755 177003710576151124711343633)
              ·
                refine ⟨132752782932113343533507725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177003710576151124711343633 132752782932113343533507725)
                ·
                  refine ⟨49782293599542503825065397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132752782932113343533507725 49782293599542503825065397)
                  ·
                    refine ⟨4667090024957109733599881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49782293599542503825065397 4667090024957109733599881)
                    ·
                      refine ⟨3500317518717832300199911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667090024957109733599881 3500317518717832300199911)
                      ·
                        rfl

theorem cell23_6816844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_6816844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816844 prefixEnd_6816844 := by exact prefixLift 6816844
  have htrace : WordTrace (prefixWord ++ tailWord_6816844) baseStart_6816844 baseEnd_6816844 := by
    simpa [prefixWord, tailWord_6816844, baseEnd_6816844] using wordTrace_append hprefix tailTrace_6816844
  have hstable : (prefixWord ++ tailWord_6816844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816844).length < 2 ^ (prefixWord ++ tailWord_6816844).sum := by decide
  have hdescent : baseEnd_6816844 < baseStart_6816844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816845 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_6816845 : Nat := 118140960795 + 6816845 * 2 ^ 59
def prefixEnd_6816845 : Nat := 4983230072969 + 3 ^ 40 * 6816845 * 2
def baseEnd_6816845 : Nat := 1166772677399495598762469

theorem tailTrace_6816845 : CollatzResearch.WordTrace tailWord_6816845 prefixEnd_6816845 1166772677399495598762469 := by
  unfold tailWord_6816845
  simp only [CollatzResearch.WordTrace]
  refine ⟨248630762988742264282467989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165753841992494842854978659 248630762988742264282467989)
  ·
    refine ⟨11654567015097293638240687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 248630762988742264282467989 11654567015097293638240687)
    ·
      refine ⟨17481850522645940457361031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11654567015097293638240687 17481850522645940457361031)
      ·
        refine ⟨26222775783968910686041547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17481850522645940457361031 26222775783968910686041547)
        ·
          refine ⟨39334163675953366029062321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26222775783968910686041547 39334163675953366029062321)
          ·
            refine ⟨29500622756965024521796741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39334163675953366029062321 29500622756965024521796741)
            ·
              refine ⟨5531366766930942097836889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29500622756965024521796741 5531366766930942097836889)
              ·
                refine ⟨4148525075198206573377667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5531366766930942097836889 4148525075198206573377667)
                ·
                  refine ⟨6222787612797309860066501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148525075198206573377667 6222787612797309860066501)
                  ·
                    refine ⟨1166772677399495598762469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6222787612797309860066501 1166772677399495598762469)
                    ·
                      rfl

theorem cell23_6816845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_6816845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816845 prefixEnd_6816845 := by exact prefixLift 6816845
  have htrace : WordTrace (prefixWord ++ tailWord_6816845) baseStart_6816845 baseEnd_6816845 := by
    simpa [prefixWord, tailWord_6816845, baseEnd_6816845] using wordTrace_append hprefix tailTrace_6816845
  have hstable : (prefixWord ++ tailWord_6816845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816845).length < 2 ^ (prefixWord ++ tailWord_6816845).sum := by decide
  have hdescent : baseEnd_6816845 < baseStart_6816845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816878 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_6816878 : Nat := 118140960795 + 6816878 * 2 ^ 59
def prefixEnd_6816878 : Nat := 4983230072969 + 3 ^ 40 * 6816878 * 2
def baseEnd_6816878 : Nat := 3500334977060085167174755

theorem tailTrace_6816878 : CollatzResearch.WordTrace tailWord_6816878 prefixEnd_6816878 3500334977060085167174755 := by
  unfold tailWord_6816878
  simp only [CollatzResearch.WordTrace]
  refine ⟨31078995824702838864802411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165754644398415140612279525 31078995824702838864802411)
  ·
    refine ⟨46618493737054258297203617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31078995824702838864802411 46618493737054258297203617)
    ·
      refine ⟨34963870302790693722902713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46618493737054258297203617 34963870302790693722902713)
      ·
        refine ⟨26222902727093020292177035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34963870302790693722902713 26222902727093020292177035)
        ·
          refine ⟨39334354090639530438265553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26222902727093020292177035 39334354090639530438265553)
          ·
            refine ⟨29500765567979647828699165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39334354090639530438265553 29500765567979647828699165)
            ·
              refine ⟨11062787087992367935762187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29500765567979647828699165 11062787087992367935762187)
              ·
                refine ⟨16594180631988551903643281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11062787087992367935762187 16594180631988551903643281)
                ·
                  refine ⟨12445635473991413927732461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16594180631988551903643281 12445635473991413927732461)
                  ·
                    refine ⟨4667113302746780222899673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12445635473991413927732461 4667113302746780222899673)
                    ·
                      refine ⟨3500334977060085167174755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667113302746780222899673 3500334977060085167174755)
                      ·
                        rfl

theorem cell23_6816878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_6816878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816878 prefixEnd_6816878 := by exact prefixLift 6816878
  have htrace : WordTrace (prefixWord ++ tailWord_6816878) baseStart_6816878 baseEnd_6816878 := by
    simpa [prefixWord, tailWord_6816878, baseEnd_6816878] using wordTrace_append hprefix tailTrace_6816878
  have hstable : (prefixWord ++ tailWord_6816878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816878).length < 2 ^ (prefixWord ++ tailWord_6816878).sum := by decide
  have hdescent : baseEnd_6816878 < baseStart_6816878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816901 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_6816901 : Nat := 118140960795 + 6816901 * 2 ^ 59
def prefixEnd_6816901 : Nat := 4983230072969 + 3 ^ 40 * 6816901 * 2
def baseEnd_6816901 : Nat := 1166782262371712859062383

theorem tailTrace_6816901 : CollatzResearch.WordTrace tailWord_6816901 prefixEnd_6816901 1166782262371712859062383 := by
  unfold tailWord_6816901
  simp only [CollatzResearch.WordTrace]
  refine ⟨248632805476539385846506557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165755203651026257231004371 248632805476539385846506557)
  ·
    refine ⟨93237302053702269692439959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248632805476539385846506557 93237302053702269692439959)
    ·
      refine ⟨139855953080553404538659939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93237302053702269692439959 139855953080553404538659939)
      ·
        refine ⟨209783929620830106807989909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139855953080553404538659939 209783929620830106807989909)
        ·
          refine ⟨9833621700976411256624527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209783929620830106807989909 9833621700976411256624527)
          ·
            refine ⟨14750432551464616884936791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9833621700976411256624527 14750432551464616884936791)
            ·
              refine ⟨22125648827196925327405187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14750432551464616884936791 22125648827196925327405187)
              ·
                refine ⟨33188473240795387991107781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22125648827196925327405187 33188473240795387991107781)
                ·
                  refine ⟨6222838732649135248332709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33188473240795387991107781 6222838732649135248332709)
                  ·
                    refine ⟨1166782262371712859062383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6222838732649135248332709 1166782262371712859062383)
                    ·
                      rfl

theorem cell23_6816901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_6816901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816901 prefixEnd_6816901 := by exact prefixLift 6816901
  have htrace : WordTrace (prefixWord ++ tailWord_6816901) baseStart_6816901 baseEnd_6816901 := by
    simpa [prefixWord, tailWord_6816901, baseEnd_6816901] using wordTrace_append hprefix tailTrace_6816901
  have hstable : (prefixWord ++ tailWord_6816901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816901).length < 2 ^ (prefixWord ++ tailWord_6816901).sum := by decide
  have hdescent : baseEnd_6816901 < baseStart_6816901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816917 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6816917 : Nat := 118140960795 + 6816917 * 2 ^ 59
def prefixEnd_6816917 : Nat := 4983230072969 + 3 ^ 40 * 6816917 * 2
def baseEnd_6816917 : Nat := 3500355002805610514587075

theorem tailTrace_6816917 : CollatzResearch.WordTrace tailWord_6816917 prefixEnd_6816917 3500355002805610514587075 := by
  unfold tailWord_6816917
  simp only [CollatzResearch.WordTrace]
  refine ⟨248633389044481420579089005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165755592696320947052726003 248633389044481420579089005)
  ·
    refine ⟨93237520891680532717158377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248633389044481420579089005 93237520891680532717158377)
    ·
      refine ⟨69928140668760399537868783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93237520891680532717158377 69928140668760399537868783)
      ·
        refine ⟨104892211003140599306803175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69928140668760399537868783 104892211003140599306803175)
        ·
          refine ⟨157338316504710898960204763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104892211003140599306803175 157338316504710898960204763)
          ·
            refine ⟨236007474757066348440307145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157338316504710898960204763 236007474757066348440307145)
            ·
              refine ⟨177005606067799761330230359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236007474757066348440307145 177005606067799761330230359)
              ·
                refine ⟨265508409101699641995345539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177005606067799761330230359 265508409101699641995345539)
                ·
                  refine ⟨398262613652549462993018309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 265508409101699641995345539 398262613652549462993018309)
                  ·
                    refine ⟨74674240059853024311190933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 398262613652549462993018309 74674240059853024311190933)
                    ·
                      refine ⟨3500355002805610514587075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74674240059853024311190933 3500355002805610514587075)
                      ·
                        rfl

theorem cell23_6816917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6816917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816917 prefixEnd_6816917 := by exact prefixLift 6816917
  have htrace : WordTrace (prefixWord ++ tailWord_6816917) baseStart_6816917 baseEnd_6816917 := by
    simpa [prefixWord, tailWord_6816917, baseEnd_6816917] using wordTrace_append hprefix tailTrace_6816917
  have hstable : (prefixWord ++ tailWord_6816917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816917).length < 2 ^ (prefixWord ++ tailWord_6816917).sum := by decide
  have hdescent : baseEnd_6816917 < baseStart_6816917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6816958 : List Nat := [4, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_6816958 : Nat := 118140960795 + 6816958 * 2 ^ 59
def prefixEnd_6816958 : Nat := 4983230072969 + 3 ^ 40 * 6816958 * 2
def baseEnd_6816958 : Nat := 3500376055512444854174387

theorem tailTrace_6816958 : CollatzResearch.WordTrace tailWord_6816958 prefixEnd_6816958 3500376055512444854174387 := by
  unfold tailWord_6816958
  simp only [CollatzResearch.WordTrace]
  refine ⟨31079360554666610572666441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165756589624888589720887685 31079360554666610572666441)
  ·
    refine ⟨23309520415999957929499831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31079360554666610572666441 23309520415999957929499831)
    ·
      refine ⟨34964280623999936894249747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23309520415999957929499831 34964280623999936894249747)
      ·
        refine ⟨52446420935999905341374621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34964280623999936894249747 52446420935999905341374621)
        ·
          refine ⟨19667407850999964503015483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52446420935999905341374621 19667407850999964503015483)
          ·
            refine ⟨29501111776499946754523225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19667407850999964503015483 29501111776499946754523225)
            ·
              refine ⟨22125833832374960065892419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29501111776499946754523225 22125833832374960065892419)
              ·
                refine ⟨33188750748562440098838629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22125833832374960065892419 33188750748562440098838629)
                ·
                  refine ⟨6222890765355457518532243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33188750748562440098838629 6222890765355457518532243)
                  ·
                    refine ⟨9334336148033186277798365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6222890765355457518532243 9334336148033186277798365)
                    ·
                      refine ⟨3500376055512444854174387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9334336148033186277798365 3500376055512444854174387)
                      ·
                        rfl

theorem cell23_6816958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_6816958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6816958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6816958 prefixEnd_6816958 := by exact prefixLift 6816958
  have htrace : WordTrace (prefixWord ++ tailWord_6816958) baseStart_6816958 baseEnd_6816958 := by
    simpa [prefixWord, tailWord_6816958, baseEnd_6816958] using wordTrace_append hprefix tailTrace_6816958
  have hstable : (prefixWord ++ tailWord_6816958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6816958).length < 2 ^ (prefixWord ++ tailWord_6816958).sum := by decide
  have hdescent : baseEnd_6816958 < baseStart_6816958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6816958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817034 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_6817034 : Nat := 118140960795 + 6817034 * 2 ^ 59
def prefixEnd_6817034 : Nat := 4983230072969 + 3 ^ 40 * 6817034 * 2
def baseEnd_6817034 : Nat := 1166805026680728852274679

theorem tailTrace_6817034 : CollatzResearch.WordTrace tailWord_6817034 prefixEnd_6817034 1166805026680728852274679 := by
  unfold tailWord_6817034
  simp only [CollatzResearch.WordTrace]
  refine ⟨62159414096264387390274539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 165758437590038366374065437 62159414096264387390274539)
  ·
    refine ⟨93239121144396581085411809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62159414096264387390274539 93239121144396581085411809)
    ·
      refine ⟨69929340858297435814058857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93239121144396581085411809 69929340858297435814058857)
      ·
        refine ⟨52447005643723076860544143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69929340858297435814058857 52447005643723076860544143)
        ·
          refine ⟨78670508465584615290816215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52447005643723076860544143 78670508465584615290816215)
          ·
            refine ⟨118005762698376922936224323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78670508465584615290816215 118005762698376922936224323)
            ·
              refine ⟨177008644047565384404336485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118005762698376922936224323 177008644047565384404336485)
              ·
                refine ⟨33189120758918509575813091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177008644047565384404336485 33189120758918509575813091)
                ·
                  refine ⟨49783681138377764363719637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33189120758918509575813091 49783681138377764363719637)
                  ·
                    refine ⟨1166805026680728852274679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49783681138377764363719637 1166805026680728852274679)
                    ·
                      rfl

theorem cell23_6817034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_6817034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817034 prefixEnd_6817034 := by exact prefixLift 6817034
  have htrace : WordTrace (prefixWord ++ tailWord_6817034) baseStart_6817034 baseEnd_6817034 := by
    simpa [prefixWord, tailWord_6817034, baseEnd_6817034] using wordTrace_append hprefix tailTrace_6817034
  have hstable : (prefixWord ++ tailWord_6817034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817034).length < 2 ^ (prefixWord ++ tailWord_6817034).sum := by decide
  have hdescent : baseEnd_6817034 < baseStart_6817034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817041 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 2, 5, 2]
def baseStart_6817041 : Nat := 118140960795 + 6817041 * 2 ^ 59
def prefixEnd_6817041 : Nat := 4983230072969 + 3 ^ 40 * 6817041 * 2
def baseEnd_6817041 : Nat := 3500418674406768029436505

theorem tailTrace_6817041 : CollatzResearch.WordTrace tailWord_6817041 prefixEnd_6817041 3500418674406768029436505 := by
  unfold tailWord_6817041
  simp only [CollatzResearch.WordTrace]
  refine ⟨248637911696032189756602977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165758607797354793171068651 248637911696032189756602977)
  ·
    refine ⟨186478433772024142317452233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 248637911696032189756602977 186478433772024142317452233)
    ·
      refine ⟨139858825329018106738089175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186478433772024142317452233 139858825329018106738089175)
      ·
        refine ⟨209788237993527160107133763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139858825329018106738089175 209788237993527160107133763)
        ·
          refine ⟨314682356990290740160700645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209788237993527160107133763 314682356990290740160700645)
          ·
            refine ⟨59002941935679513780131371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 314682356990290740160700645 59002941935679513780131371)
            ·
              refine ⟨88504412903519270670197057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59002941935679513780131371 88504412903519270670197057)
              ·
                refine ⟨66378309677639453002647793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88504412903519270670197057 66378309677639453002647793)
                ·
                  refine ⟨49783732258229589751985845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66378309677639453002647793 49783732258229589751985845)
                  ·
                    refine ⟨4667224899209024039248673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49783732258229589751985845 4667224899209024039248673)
                    ·
                      refine ⟨3500418674406768029436505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667224899209024039248673 3500418674406768029436505)
                      ·
                        rfl

theorem cell23_6817041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_6817041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817041 prefixEnd_6817041 := by exact prefixLift 6817041
  have htrace : WordTrace (prefixWord ++ tailWord_6817041) baseStart_6817041 baseEnd_6817041 := by
    simpa [prefixWord, tailWord_6817041, baseEnd_6817041] using wordTrace_append hprefix tailTrace_6817041
  have hstable : (prefixWord ++ tailWord_6817041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817041).length < 2 ^ (prefixWord ++ tailWord_6817041).sum := by decide
  have hdescent : baseEnd_6817041 < baseStart_6817041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817108 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_6817108 : Nat := 118140960795 + 6817108 * 2 ^ 59
def prefixEnd_6817108 : Nat := 4983230072969 + 3 ^ 40 * 6817108 * 2
def baseEnd_6817108 : Nat := 3500453077610619267298697

theorem tailTrace_6817108 : CollatzResearch.WordTrace tailWord_6817108 prefixEnd_6817108 3500453077610619267298697 := by
  unfold tailWord_6817108
  simp only [CollatzResearch.WordTrace]
  refine ⟨124320177693394730099645989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165760236924526306799527985 124320177693394730099645989)
  ·
    refine ⟨23310033317511511893683623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124320177693394730099645989 23310033317511511893683623)
    ·
      refine ⟨34965049976267267840525435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23310033317511511893683623 34965049976267267840525435)
      ·
        refine ⟨52447574964400901760788153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34965049976267267840525435 52447574964400901760788153)
        ·
          refine ⟨39335681223300676320591115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52447574964400901760788153 39335681223300676320591115)
          ·
            refine ⟨59003521834951014480886673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39335681223300676320591115 59003521834951014480886673)
            ·
              refine ⟨44252641376213260860665005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59003521834951014480886673 44252641376213260860665005)
              ·
                refine ⟨16594740516079972822749377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44252641376213260860665005 16594740516079972822749377)
                ·
                  refine ⟨12446055387059979617062033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16594740516079972822749377 12446055387059979617062033)
                  ·
                    refine ⟨9334541540294984712796525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12446055387059979617062033 9334541540294984712796525)
                    ·
                      refine ⟨3500453077610619267298697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9334541540294984712796525 3500453077610619267298697)
                      ·
                        rfl

theorem cell23_6817108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_6817108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817108 prefixEnd_6817108 := by exact prefixLift 6817108
  have htrace : WordTrace (prefixWord ++ tailWord_6817108) baseStart_6817108 baseEnd_6817108 := by
    simpa [prefixWord, tailWord_6817108, baseEnd_6817108] using wordTrace_append hprefix tailTrace_6817108
  have hstable : (prefixWord ++ tailWord_6817108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817108).length < 2 ^ (prefixWord ++ tailWord_6817108).sum := by decide
  have hdescent : baseEnd_6817108 < baseStart_6817108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817132 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 1, 4]
def baseStart_6817132 : Nat := 118140960795 + 6817132 * 2 ^ 59
def prefixEnd_6817132 : Nat := 4983230072969 + 3 ^ 40 * 6817132 * 2
def baseEnd_6817132 : Nat := 1166821800382109057799529

theorem tailTrace_6817132 : CollatzResearch.WordTrace tailWord_6817132 prefixEnd_6817132 1166821800382109057799529 := by
  unfold tailWord_6817132
  simp only [CollatzResearch.WordTrace]
  refine ⟨124320615369351256149082825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165760820492468341532110433 124320615369351256149082825)
  ·
    refine ⟨93240461527013442111812119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124320615369351256149082825 93240461527013442111812119)
    ·
      refine ⟨139860692290520163167718179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93240461527013442111812119 139860692290520163167718179)
      ·
        refine ⟨209791038435780244751577269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139860692290520163167718179 209791038435780244751577269)
        ·
          refine ⟨19667909853354397945460369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 209791038435780244751577269 19667909853354397945460369)
          ·
            refine ⟨14750932390015798459095277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19667909853354397945460369 14750932390015798459095277)
            ·
              refine ⟨5531599646255924422160729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14750932390015798459095277 5531599646255924422160729)
              ·
                refine ⟨4148699734691943316620547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5531599646255924422160729 4148699734691943316620547)
                ·
                  refine ⟨6223049602037914974930821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148699734691943316620547 6223049602037914974930821)
                  ·
                    refine ⟨1166821800382109057799529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6223049602037914974930821 1166821800382109057799529)
                    ·
                      rfl

theorem cell23_6817132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 1, 4].length) (baseStart_6817132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817132 prefixEnd_6817132 := by exact prefixLift 6817132
  have htrace : WordTrace (prefixWord ++ tailWord_6817132) baseStart_6817132 baseEnd_6817132 := by
    simpa [prefixWord, tailWord_6817132, baseEnd_6817132] using wordTrace_append hprefix tailTrace_6817132
  have hstable : (prefixWord ++ tailWord_6817132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817132).length < 2 ^ (prefixWord ++ tailWord_6817132).sum := by decide
  have hdescent : baseEnd_6817132 < baseStart_6817132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817144 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_6817144 : Nat := 118140960795 + 6817144 * 2 ^ 59
def prefixEnd_6817144 : Nat := 4983230072969 + 3 ^ 40 * 6817144 * 2
def baseEnd_6817144 : Nat := 3500471562914181126448531

theorem tailTrace_6817144 : CollatzResearch.WordTrace tailWord_6817144 prefixEnd_6817144 3500471562914181126448531 := by
  unfold tailWord_6817144
  simp only [CollatzResearch.WordTrace]
  refine ⟨124320834207329519173801243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165761112276439358898401657 124320834207329519173801243)
  ·
    refine ⟨186481251310994278760701865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124320834207329519173801243 186481251310994278760701865)
    ·
      refine ⟨139860938483245709070526399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186481251310994278760701865 139860938483245709070526399)
      ·
        refine ⟨209791407724868563605789599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139860938483245709070526399 209791407724868563605789599)
        ·
          refine ⟨314687111587302845408684399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209791407724868563605789599 314687111587302845408684399)
          ·
            refine ⟨472030667380954268113026599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314687111587302845408684399 472030667380954268113026599)
            ·
              refine ⟨708046001071431402169539899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472030667380954268113026599 708046001071431402169539899)
              ·
                refine ⟨1062069001607147103254309849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 708046001071431402169539899 1062069001607147103254309849)
                ·
                  refine ⟨796551751205360327440732387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1062069001607147103254309849 796551751205360327440732387)
                  ·
                    refine ⟨1194827626808040491161098581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 796551751205360327440732387 1194827626808040491161098581)
                    ·
                      refine ⟨3500471562914181126448531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1194827626808040491161098581 3500471562914181126448531)
                      ·
                        rfl

theorem cell23_6817144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_6817144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817144 prefixEnd_6817144 := by exact prefixLift 6817144
  have htrace : WordTrace (prefixWord ++ tailWord_6817144) baseStart_6817144 baseEnd_6817144 := by
    simpa [prefixWord, tailWord_6817144, baseEnd_6817144] using wordTrace_append hprefix tailTrace_6817144
  have hstable : (prefixWord ++ tailWord_6817144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817144).length < 2 ^ (prefixWord ++ tailWord_6817144).sum := by decide
  have hdescent : baseEnd_6817144 < baseStart_6817144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817148 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_6817148 : Nat := 118140960795 + 6817148 * 2 ^ 59
def prefixEnd_6817148 : Nat := 4983230072969 + 3 ^ 40 * 6817148 * 2
def baseEnd_6817148 : Nat := 3500473616836799110798513

theorem tailTrace_6817148 : CollatzResearch.WordTrace tailWord_6817148 prefixEnd_6817148 3500473616836799110798513 := by
  unfold tailWord_6817148
  simp only [CollatzResearch.WordTrace]
  refine ⟨124320907153322273515374049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165761209537763031353832065 124320907153322273515374049)
  ·
    refine ⟨93240680364991705136530537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124320907153322273515374049 93240680364991705136530537)
    ·
      refine ⟨69930510273743778852397903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93240680364991705136530537 69930510273743778852397903)
      ·
        refine ⟨104895765410615668278596855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69930510273743778852397903 104895765410615668278596855)
        ·
          refine ⟨157343648115923502417895283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104895765410615668278596855 157343648115923502417895283)
          ·
            refine ⟨236015472173885253626842925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157343648115923502417895283 236015472173885253626842925)
            ·
              refine ⟨88505802065206970110066097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236015472173885253626842925 88505802065206970110066097)
              ·
                refine ⟨66379351548905227582549573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88505802065206970110066097 66379351548905227582549573)
                ·
                  refine ⟨12446128415419730171728045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66379351548905227582549573 12446128415419730171728045)
                  ·
                    refine ⟨4667298155782398814398017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12446128415419730171728045 4667298155782398814398017)
                    ·
                      refine ⟨3500473616836799110798513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667298155782398814398017 3500473616836799110798513)
                      ·
                        rfl

theorem cell23_6817148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_6817148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817148 prefixEnd_6817148 := by exact prefixLift 6817148
  have htrace : WordTrace (prefixWord ++ tailWord_6817148) baseStart_6817148 baseEnd_6817148 := by
    simpa [prefixWord, tailWord_6817148, baseEnd_6817148] using wordTrace_append hprefix tailTrace_6817148
  have hstable : (prefixWord ++ tailWord_6817148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817148).length < 2 ^ (prefixWord ++ tailWord_6817148).sum := by decide
  have hdescent : baseEnd_6817148 < baseStart_6817148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817205 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_6817205 : Nat := 118140960795 + 6817205 * 2 ^ 59
def prefixEnd_6817205 : Nat := 4983230072969 + 3 ^ 40 * 6817205 * 2
def baseEnd_6817205 : Nat := 1166834295078035129261917

theorem tailTrace_6817205 : CollatzResearch.WordTrace tailWord_6817205 prefixEnd_6817205 1166834295078035129261917 := by
  unfold tailWord_6817205
  simp only [CollatzResearch.WordTrace]
  refine ⟨248643893267438045765573069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165762595511625363843715379 248643893267438045765573069)
  ·
    refine ⟨93241459975289267162089901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248643893267438045765573069 93241459975289267162089901)
    ·
      refine ⟨34965547490733475185783713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93241459975289267162089901 34965547490733475185783713)
      ·
        refine ⟨26224160618050106389337785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34965547490733475185783713 26224160618050106389337785)
        ·
          refine ⟨19668120463537579792003339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26224160618050106389337785 19668120463537579792003339)
          ·
            refine ⟨29502180695306369688005009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19668120463537579792003339 29502180695306369688005009)
            ·
              refine ⟨22126635521479777266003757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29502180695306369688005009 22126635521479777266003757)
              ·
                refine ⟨8297488320554916474751409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22126635521479777266003757 8297488320554916474751409)
                ·
                  refine ⟨6223116240416187356063557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8297488320554916474751409 6223116240416187356063557)
                  ·
                    refine ⟨1166834295078035129261917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6223116240416187356063557 1166834295078035129261917)
                    ·
                      rfl

theorem cell23_6817205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_6817205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817205 prefixEnd_6817205 := by exact prefixLift 6817205
  have htrace : WordTrace (prefixWord ++ tailWord_6817205) baseStart_6817205 baseEnd_6817205 := by
    simpa [prefixWord, tailWord_6817205, baseEnd_6817205] using wordTrace_append hprefix tailTrace_6817205
  have hstable : (prefixWord ++ tailWord_6817205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817205).length < 2 ^ (prefixWord ++ tailWord_6817205).sum := by decide
  have hdescent : baseEnd_6817205 < baseStart_6817205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817272 : List Nat := [2, 1, 2, 1, 1, 6, 2, 2, 1, 3, 2]
def baseStart_6817272 : Nat := 118140960795 + 6817272 * 2 ^ 59
def prefixEnd_6817272 : Nat := 4983230072969 + 3 ^ 40 * 6817272 * 2
def baseEnd_6817272 : Nat := 3500537288437956625647943

theorem tailTrace_6817272 : CollatzResearch.WordTrace tailWord_6817272 prefixEnd_6817272 3500537288437956625647943 := by
  unfold tailWord_6817272
  simp only [CollatzResearch.WordTrace]
  refine ⟨124323168479097658104131035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165764224638796877472174713 124323168479097658104131035)
  ·
    refine ⟨186484752718646487156196553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124323168479097658104131035 186484752718646487156196553)
    ·
      refine ⟨139863564538984865367147415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186484752718646487156196553 139863564538984865367147415)
      ·
        refine ⟨209795346808477298050721123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139863564538984865367147415 209795346808477298050721123)
        ·
          refine ⟨314693020212715947076081685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209795346808477298050721123 314693020212715947076081685)
          ·
            refine ⟨14751235322471060019191329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 314693020212715947076081685 14751235322471060019191329)
            ·
              refine ⟨11063426491853295014393497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14751235322471060019191329 11063426491853295014393497)
              ·
                refine ⟨8297569868889971260795123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11063426491853295014393497 8297569868889971260795123)
                ·
                  refine ⟨12446354803334956891192685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297569868889971260795123 12446354803334956891192685)
                  ·
                    refine ⟨4667383051250608834197257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12446354803334956891192685 4667383051250608834197257)
                    ·
                      refine ⟨3500537288437956625647943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4667383051250608834197257 3500537288437956625647943)
                      ·
                        rfl

theorem cell23_6817272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 2, 1, 3, 2].length) (baseStart_6817272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817272 prefixEnd_6817272 := by exact prefixLift 6817272
  have htrace : WordTrace (prefixWord ++ tailWord_6817272) baseStart_6817272 baseEnd_6817272 := by
    simpa [prefixWord, tailWord_6817272, baseEnd_6817272] using wordTrace_append hprefix tailTrace_6817272
  have hstable : (prefixWord ++ tailWord_6817272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817272).length < 2 ^ (prefixWord ++ tailWord_6817272).sum := by decide
  have hdescent : baseEnd_6817272 < baseStart_6817272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817358 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_6817358 : Nat := 118140960795 + 6817358 * 2 ^ 59
def prefixEnd_6817358 : Nat := 4983230072969 + 3 ^ 40 * 6817358 * 2
def baseEnd_6817358 : Nat := 3500581447774243289172547

theorem tailTrace_6817358 : CollatzResearch.WordTrace tailWord_6817358 prefixEnd_6817358 3500581447774243289172547 := by
  unfold tailWord_6817358
  simp only [CollatzResearch.WordTrace]
  refine ⟨31081184204485469111986591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 165766315757255835263928485 31081184204485469111986591)
  ·
    refine ⟨46621776306728203667979887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31081184204485469111986591 46621776306728203667979887)
    ·
      refine ⟨69932664460092305501969831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46621776306728203667979887 69932664460092305501969831)
      ·
        refine ⟨104898996690138458252954747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69932664460092305501969831 104898996690138458252954747)
        ·
          refine ⟨157348495035207687379432121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104898996690138458252954747 157348495035207687379432121)
          ·
            refine ⟨118011371276405765534574091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157348495035207687379432121 118011371276405765534574091)
            ·
              refine ⟨177017056914608648301861137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118011371276405765534574091 177017056914608648301861137)
              ·
                refine ⟨132762792685956486226395853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177017056914608648301861137 132762792685956486226395853)
                ·
                  refine ⟨49786047257233682334898445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132762792685956486226395853 49786047257233682334898445)
                  ·
                    refine ⟨18669767721462630875586917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49786047257233682334898445 18669767721462630875586917)
                    ·
                      refine ⟨3500581447774243289172547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18669767721462630875586917 3500581447774243289172547)
                      ·
                        rfl

theorem cell23_6817358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_6817358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817358 prefixEnd_6817358 := by exact prefixLift 6817358
  have htrace : WordTrace (prefixWord ++ tailWord_6817358) baseStart_6817358 baseEnd_6817358 := by
    simpa [prefixWord, tailWord_6817358, baseEnd_6817358] using wordTrace_append hprefix tailTrace_6817358
  have hstable : (prefixWord ++ tailWord_6817358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817358).length < 2 ^ (prefixWord ++ tailWord_6817358).sum := by decide
  have hdescent : baseEnd_6817358 < baseStart_6817358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817389 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_6817389 : Nat := 118140960795 + 6817389 * 2 ^ 59
def prefixEnd_6817389 : Nat := 4983230072969 + 3 ^ 40 * 6817389 * 2
def baseEnd_6817389 : Nat := 1166865788558177555961635

theorem tailTrace_6817389 : CollatzResearch.WordTrace tailWord_6817389 prefixEnd_6817389 1166865788558177555961635 := by
  unfold tailWord_6817389
  simp only [CollatzResearch.WordTrace]
  refine ⟨248650604298771445190271221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165767069532514296793514147 248650604298771445190271221)
  ·
    refine ⟨23310994153009822986587927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 248650604298771445190271221 23310994153009822986587927)
    ·
      refine ⟨34966491229514734479881891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23310994153009822986587927 34966491229514734479881891)
      ·
        refine ⟨52449736844272101719822837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34966491229514734479881891 52449736844272101719822837)
        ·
          refine ⟨4917162829150509536233391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52449736844272101719822837 4917162829150509536233391)
          ·
            refine ⟨7375744243725764304350087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4917162829150509536233391 7375744243725764304350087)
            ·
              refine ⟨11063616365588646456525131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7375744243725764304350087 11063616365588646456525131)
              ·
                refine ⟨16595424548382969684787697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11063616365588646456525131 16595424548382969684787697)
                ·
                  refine ⟨12446568411287227263590773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16595424548382969684787697 12446568411287227263590773)
                  ·
                    refine ⟨1166865788558177555961635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12446568411287227263590773 1166865788558177555961635)
                    ·
                      rfl

theorem cell23_6817389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_6817389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817389 prefixEnd_6817389 := by exact prefixLift 6817389
  have htrace : WordTrace (prefixWord ++ tailWord_6817389) baseStart_6817389 baseEnd_6817389 := by
    simpa [prefixWord, tailWord_6817389, baseEnd_6817389] using wordTrace_append hprefix tailTrace_6817389
  have hstable : (prefixWord ++ tailWord_6817389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817389).length < 2 ^ (prefixWord ++ tailWord_6817389).sum := by decide
  have hdescent : baseEnd_6817389 < baseStart_6817389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817392 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4]
def baseStart_6817392 : Nat := 118140960795 + 6817392 * 2 ^ 59
def prefixEnd_6817392 : Nat := 4983230072969 + 3 ^ 40 * 6817392 * 2
def baseEnd_6817392 : Nat := 3500598906116496156147391

theorem tailTrace_6817392 : CollatzResearch.WordTrace tailWord_6817392 prefixEnd_6817392 3500598906116496156147391 := by
  unfold tailWord_6817392
  simp only [CollatzResearch.WordTrace]
  refine ⟨124325356858880288351315215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165767142478507051135086953 124325356858880288351315215)
  ·
    refine ⟨186488035288320432526972823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124325356858880288351315215 186488035288320432526972823)
    ·
      refine ⟨279732052932480648790459235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186488035288320432526972823 279732052932480648790459235)
      ·
        refine ⟨419598079398720973185688853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279732052932480648790459235 419598079398720973185688853)
        ·
          refine ⟨19668659971815045618079165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 419598079398720973185688853 19668659971815045618079165)
          ·
            refine ⟨7375747489430642106779687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19668659971815045618079165 7375747489430642106779687)
            ·
              refine ⟨11063621234145963160169531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7375747489430642106779687 11063621234145963160169531)
              ·
                refine ⟨16595431851218944740254297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11063621234145963160169531 16595431851218944740254297)
                ·
                  refine ⟨12446573888414208555190723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16595431851218944740254297 12446573888414208555190723)
                  ·
                    refine ⟨18669860832621312832786085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12446573888414208555190723 18669860832621312832786085)
                    ·
                      refine ⟨3500598906116496156147391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18669860832621312832786085 3500598906116496156147391)
                      ·
                        rfl

theorem cell23_6817392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 4].length) (baseStart_6817392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817392 prefixEnd_6817392 := by exact prefixLift 6817392
  have htrace : WordTrace (prefixWord ++ tailWord_6817392) baseStart_6817392 baseEnd_6817392 := by
    simpa [prefixWord, tailWord_6817392, baseEnd_6817392] using wordTrace_append hprefix tailTrace_6817392
  have hstable : (prefixWord ++ tailWord_6817392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817392).length < 2 ^ (prefixWord ++ tailWord_6817392).sum := by decide
  have hdescent : baseEnd_6817392 < baseStart_6817392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817415 : List Nat := [1, 1, 4, 2, 1, 3, 3, 2, 6]
def baseStart_6817415 : Nat := 118140960795 + 6817415 * 2 ^ 59
def prefixEnd_6817415 : Nat := 4983230072969 + 3 ^ 40 * 6817415 * 2
def baseEnd_6817415 : Nat := 388956746241283285128865

theorem tailTrace_6817415 : CollatzResearch.WordTrace tailWord_6817415 prefixEnd_6817415 388956746241283285128865 := by
  unfold tailWord_6817415
  simp only [CollatzResearch.WordTrace]
  refine ⟨248651552596677251630717699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165767701731118167753811799 248651552596677251630717699)
  ·
    refine ⟨372977328895015877446076549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 248651552596677251630717699 372977328895015877446076549)
    ·
      refine ⟨69933249167815477021139353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 372977328895015877446076549 69933249167815477021139353)
      ·
        refine ⟨52449936875861607765854515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69933249167815477021139353 52449936875861607765854515)
        ·
          refine ⟨78674905313792411648781773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52449936875861607765854515 78674905313792411648781773)
          ·
            refine ⟨29503089492672154368293165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78674905313792411648781773 29503089492672154368293165)
            ·
              refine ⟨11063658559752057888109937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29503089492672154368293165 11063658559752057888109937)
              ·
                refine ⟨8297743919814043416082453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11063658559752057888109937 8297743919814043416082453)
                ·
                  refine ⟨388956746241283285128865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8297743919814043416082453 388956746241283285128865)
                  ·
                    rfl

theorem cell23_6817415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 6].length) (baseStart_6817415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817415 prefixEnd_6817415 := by exact prefixLift 6817415
  have htrace : WordTrace (prefixWord ++ tailWord_6817415) baseStart_6817415 baseEnd_6817415 := by
    simpa [prefixWord, tailWord_6817415, baseEnd_6817415] using wordTrace_append hprefix tailTrace_6817415
  have hstable : (prefixWord ++ tailWord_6817415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817415).length < 2 ^ (prefixWord ++ tailWord_6817415).sum := by decide
  have hdescent : baseEnd_6817415 < baseStart_6817415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817432 : List Nat := [2, 1, 2, 4, 1, 3, 3, 1, 6]
def baseStart_6817432 : Nat := 118140960795 + 6817432 * 2 ^ 59
def prefixEnd_6817432 : Nat := 4983230072969 + 3 ^ 40 * 6817432 * 2
def baseEnd_6817432 : Nat := 388957716149186222183023

theorem tailTrace_6817432 : CollatzResearch.WordTrace tailWord_6817432 prefixEnd_6817432 388957716149186222183023 := by
  unfold tailWord_6817432
  simp only [CollatzResearch.WordTrace]
  refine ⟨124326086318807831767043275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 165768115091743775689391033 124326086318807831767043275)
  ·
    refine ⟨186489129478211747650564913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124326086318807831767043275 186489129478211747650564913)
    ·
      refine ⟨139866847108658810737923685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186489129478211747650564913 139866847108658810737923685)
      ·
        refine ⟨26225033832873527013360691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139866847108658810737923685 26225033832873527013360691)
        ·
          refine ⟨39337550749310290520041037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26225033832873527013360691 39337550749310290520041037)
          ·
            refine ⟨14751581530991358945015389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39337550749310290520041037 14751581530991358945015389)
            ·
              refine ⟨5531843074121759604380771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14751581530991358945015389 5531843074121759604380771)
              ·
                refine ⟨8297764611182639406571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5531843074121759604380771 8297764611182639406571157)
                ·
                  refine ⟨388957716149186222183023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8297764611182639406571157 388957716149186222183023)
                  ·
                    rfl

theorem cell23_6817432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 6].length) (baseStart_6817432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817432 prefixEnd_6817432 := by exact prefixLift 6817432
  have htrace : WordTrace (prefixWord ++ tailWord_6817432) baseStart_6817432 baseEnd_6817432 := by
    simpa [prefixWord, tailWord_6817432, baseEnd_6817432] using wordTrace_append hprefix tailTrace_6817432
  have hstable : (prefixWord ++ tailWord_6817432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817432).length < 2 ^ (prefixWord ++ tailWord_6817432).sum := by decide
  have hdescent : baseEnd_6817432 < baseStart_6817432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6817445 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_6817445 : Nat := 118140960795 + 6817445 * 2 ^ 59
def prefixEnd_6817445 : Nat := 4983230072969 + 3 ^ 40 * 6817445 * 2
def baseEnd_6817445 : Nat := 1166875373530394816261549

theorem tailTrace_6817445 : CollatzResearch.WordTrace tailWord_6817445 prefixEnd_6817445 1166875373530394816261549 := by
  unfold tailWord_6817445
  simp only [CollatzResearch.WordTrace]
  refine ⟨248652646786568566754309789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 165768431191045711169539859 248652646786568566754309789)
  ·
    refine ⟨93244742544963212532866171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 248652646786568566754309789 93244742544963212532866171)
    ·
      refine ⟨139867113817444818799299257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93244742544963212532866171 139867113817444818799299257)
      ·
        refine ⟨104900335363083614099474443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139867113817444818799299257 104900335363083614099474443)
        ·
          refine ⟨157350503044625421149211665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104900335363083614099474443 157350503044625421149211665)
          ·
            refine ⟨118012877283469065861908749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157350503044625421149211665 118012877283469065861908749)
            ·
              refine ⟨44254828981300899698215781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118012877283469065861908749 44254828981300899698215781)
              ·
                refine ⟨8297780433993918693415459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44254828981300899698215781 8297780433993918693415459)
                ·
                  refine ⟨12446670650990878040123189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8297780433993918693415459 12446670650990878040123189)
                  ·
                    refine ⟨1166875373530394816261549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12446670650990878040123189 1166875373530394816261549)
                    ·
                      rfl

theorem cell23_6817445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_6817445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6817445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6817445 prefixEnd_6817445 := by exact prefixLift 6817445
  have htrace : WordTrace (prefixWord ++ tailWord_6817445) baseStart_6817445 baseEnd_6817445 := by
    simpa [prefixWord, tailWord_6817445, baseEnd_6817445] using wordTrace_append hprefix tailTrace_6817445
  have hstable : (prefixWord ++ tailWord_6817445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6817445).length < 2 ^ (prefixWord ++ tailWord_6817445).sum := by decide
  have hdescent : baseEnd_6817445 < baseStart_6817445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6817445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
