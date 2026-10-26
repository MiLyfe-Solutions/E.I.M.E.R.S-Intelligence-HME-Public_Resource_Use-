import V185TrunkScan22Chunk345

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3087174 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3087174 : Nat := 118140960795 + 3087174 * 2 ^ 59
def prefixEnd_3087174 : Nat := 4983230072969 + 3 ^ 40 * 3087174 * 2
def baseEnd_3087174 : Nat := 1056802750708939767484901

theorem tailTrace_3087174 : CollatzResearch.WordTrace tailWord_3087174 prefixEnd_3087174 1056802750708939767484901 := by
  unfold tailWord_3087174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3518702691178228755875143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75065657411802213458669717 3518702691178228755875143)
  ·
    refine ⟨5278054036767343133812715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3518702691178228755875143 5278054036767343133812715)
    ·
      refine ⟨7917081055151014700719073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5278054036767343133812715 7917081055151014700719073)
      ·
        refine ⟨5937810791363261025539305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7917081055151014700719073 5937810791363261025539305)
        ·
          refine ⟨4453358093522445769154479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5937810791363261025539305 4453358093522445769154479)
          ·
            refine ⟨6680037140283668653731719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453358093522445769154479 6680037140283668653731719)
            ·
              refine ⟨10020055710425502980597579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680037140283668653731719 10020055710425502980597579)
              ·
                refine ⟨15030083565638254470896369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10020055710425502980597579 15030083565638254470896369)
                ·
                  refine ⟨11272562674228690853172277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15030083565638254470896369 11272562674228690853172277)
                  ·
                    refine ⟨1056802750708939767484901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11272562674228690853172277 1056802750708939767484901)
                    ·
                      rfl

theorem cell22_3087174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3087174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087174 prefixEnd_3087174 := by exact prefixLift 3087174
  have htrace : WordTrace (prefixWord ++ tailWord_3087174) baseStart_3087174 baseEnd_3087174 := by
    simpa [prefixWord, tailWord_3087174, baseEnd_3087174] using wordTrace_append hprefix tailTrace_3087174
  have hstable : (prefixWord ++ tailWord_3087174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087174).length < 2 ^ (prefixWord ++ tailWord_3087174).sum := by decide
  have hdescent : baseEnd_3087174 < baseStart_3087174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087228 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_3087228 : Nat := 118140960795 + 3087228 * 2 ^ 59
def prefixEnd_3087228 : Nat := 4983230072969 + 3 ^ 40 * 3087228 * 2
def baseEnd_3087228 : Nat := 1056821236012501626634735

theorem tailTrace_3087228 : CollatzResearch.WordTrace tailWord_3087228 prefixEnd_3087228 1056821236012501626634735 := by
  unfold tailWord_3087228
  simp only [CollatzResearch.WordTrace]
  refine ⟨56300227829753843705235169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75066970439671791606980225 56300227829753843705235169)
  ·
    refine ⟨42225170872315382778926377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56300227829753843705235169 42225170872315382778926377)
    ·
      refine ⟨31668878154236537084194783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42225170872315382778926377 31668878154236537084194783)
      ·
        refine ⟨47503317231354805626292175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31668878154236537084194783 47503317231354805626292175)
        ·
          refine ⟨71254975847032208439438263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47503317231354805626292175 71254975847032208439438263)
          ·
            refine ⟨106882463770548312659157395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71254975847032208439438263 106882463770548312659157395)
            ·
              refine ⟨160323695655822468988736093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106882463770548312659157395 160323695655822468988736093)
              ·
                refine ⟨60121385870933425870776035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 160323695655822468988736093 60121385870933425870776035)
                ·
                  refine ⟨90182078806400138806164053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60121385870933425870776035 90182078806400138806164053)
                  ·
                    refine ⟨1056821236012501626634735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90182078806400138806164053 1056821236012501626634735)
                    ·
                      rfl

theorem cell22_3087228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_3087228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087228 prefixEnd_3087228 := by exact prefixLift 3087228
  have htrace : WordTrace (prefixWord ++ tailWord_3087228) baseStart_3087228 baseEnd_3087228 := by
    simpa [prefixWord, tailWord_3087228, baseEnd_3087228] using wordTrace_append hprefix tailTrace_3087228
  have hstable : (prefixWord ++ tailWord_3087228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087228).length < 2 ^ (prefixWord ++ tailWord_3087228).sum := by decide
  have hdescent : baseEnd_3087228 < baseStart_3087228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087264 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 1, 3]
def baseStart_3087264 : Nat := 118140960795 + 3087264 * 2 ^ 59
def prefixEnd_3087264 : Nat := 4983230072969 + 3 ^ 40 * 3087264 * 2
def baseEnd_3087264 : Nat := 1056833559548209532734625

theorem tailTrace_3087264 : CollatzResearch.WordTrace tailWord_3087264 prefixEnd_3087264 1056833559548209532734625 := by
  unfold tailWord_3087264
  simp only [CollatzResearch.WordTrace]
  refine ⟨56300884343688632779390423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75067845791584843705853897 56300884343688632779390423)
  ·
    refine ⟨84451326515532949169085635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56300884343688632779390423 84451326515532949169085635)
    ·
      refine ⟨126676989773299423753628453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84451326515532949169085635 126676989773299423753628453)
      ·
        refine ⟨23751935582493641953805335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126676989773299423753628453 23751935582493641953805335)
        ·
          refine ⟨35627903373740462930708003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23751935582493641953805335 35627903373740462930708003)
          ·
            refine ⟨53441855060610694396062005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35627903373740462930708003 53441855060610694396062005)
            ·
              refine ⟨5010173911932252599630813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53441855060610694396062005 5010173911932252599630813)
              ·
                refine ⟨1878815216974594724861555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5010173911932252599630813 1878815216974594724861555)
                ·
                  refine ⟨2818222825461892087292333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878815216974594724861555 2818222825461892087292333)
                  ·
                    refine ⟨1056833559548209532734625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818222825461892087292333 1056833559548209532734625)
                    ·
                      rfl

theorem cell22_3087264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_3087264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087264 prefixEnd_3087264 := by exact prefixLift 3087264
  have htrace : WordTrace (prefixWord ++ tailWord_3087264) baseStart_3087264 baseEnd_3087264 := by
    simpa [prefixWord, tailWord_3087264, baseEnd_3087264] using wordTrace_append hprefix tailTrace_3087264
  have hstable : (prefixWord ++ tailWord_3087264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087264).length < 2 ^ (prefixWord ++ tailWord_3087264).sum := by decide
  have hdescent : baseEnd_3087264 < baseStart_3087264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087281 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 3, 3]
def baseStart_3087281 : Nat := 118140960795 + 3087281 * 2 ^ 59
def prefixEnd_3087281 : Nat := 4983230072969 + 3 ^ 40 * 3087281 * 2
def baseEnd_3087281 : Nat := 1056839378995627155059573

theorem tailTrace_3087281 : CollatzResearch.WordTrace tailWord_3087281 prefixEnd_3087281 1056839378995627155059573 := by
  unfold tailWord_3087281
  simp only [CollatzResearch.WordTrace]
  refine ⟨112602388728315677462149697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75068259152210451641433131 112602388728315677462149697)
  ·
    refine ⟨84451791546236758096612273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112602388728315677462149697 84451791546236758096612273)
    ·
      refine ⟨63338843659677568572459205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84451791546236758096612273 63338843659677568572459205)
      ·
        refine ⟨11876033186189544107336101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63338843659677568572459205 11876033186189544107336101)
        ·
          refine ⟨2226756222410539520125519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11876033186189544107336101 2226756222410539520125519)
          ·
            refine ⟨3340134333615809280188279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226756222410539520125519 3340134333615809280188279)
            ·
              refine ⟨5010201500423713920282419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3340134333615809280188279 5010201500423713920282419)
              ·
                refine ⟨7515302250635570880423629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010201500423713920282419 7515302250635570880423629)
                ·
                  refine ⟨2818238343988339080158861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7515302250635570880423629 2818238343988339080158861)
                  ·
                    refine ⟨1056839378995627155059573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818238343988339080158861 1056839378995627155059573)
                    ·
                      rfl

theorem cell22_3087281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_3087281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087281 prefixEnd_3087281 := by exact prefixLift 3087281
  have htrace : WordTrace (prefixWord ++ tailWord_3087281) baseStart_3087281 baseEnd_3087281 := by
    simpa [prefixWord, tailWord_3087281, baseEnd_3087281] using wordTrace_append hprefix tailTrace_3087281
  have hstable : (prefixWord ++ tailWord_3087281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087281).length < 2 ^ (prefixWord ++ tailWord_3087281).sum := by decide
  have hdescent : baseEnd_3087281 < baseStart_3087281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087290 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_3087290 : Nat := 118140960795 + 3087290 * 2 ^ 59
def prefixEnd_3087290 : Nat := 4983230072969 + 3 ^ 40 * 3087290 * 2
def baseEnd_3087290 : Nat := 1056842459879554131584545

theorem tailTrace_3087290 : CollatzResearch.WordTrace tailWord_3087290 prefixEnd_3087290 1056842459879554131584545 := by
  unfold tailWord_3087290
  simp only [CollatzResearch.WordTrace]
  refine ⟨28150679246320767999806831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75068477990188714666151549 28150679246320767999806831)
  ·
    refine ⟨42226018869481151999710247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28150679246320767999806831 42226018869481151999710247)
    ·
      refine ⟨63339028304221727999565371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42226018869481151999710247 63339028304221727999565371)
      ·
        refine ⟨95008542456332591999348057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63339028304221727999565371 95008542456332591999348057)
        ·
          refine ⟨71256406842249443999511043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95008542456332591999348057 71256406842249443999511043)
          ·
            refine ⟨106884610263374165999266565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71256406842249443999511043 106884610263374165999266565)
            ·
              refine ⟨20040864424382656124862481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106884610263374165999266565 20040864424382656124862481)
              ·
                refine ⟨15030648318286992093646861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20040864424382656124862481 15030648318286992093646861)
                ·
                  refine ⟨5636493119357622035117573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15030648318286992093646861 5636493119357622035117573)
                  ·
                    refine ⟨1056842459879554131584545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636493119357622035117573 1056842459879554131584545)
                    ·
                      rfl

theorem cell22_3087290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_3087290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087290 prefixEnd_3087290 := by exact prefixLift 3087290
  have htrace : WordTrace (prefixWord ++ tailWord_3087290) baseStart_3087290 baseEnd_3087290 := by
    simpa [prefixWord, tailWord_3087290, baseEnd_3087290] using wordTrace_append hprefix tailTrace_3087290
  have hstable : (prefixWord ++ tailWord_3087290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087290).length < 2 ^ (prefixWord ++ tailWord_3087290).sum := by decide
  have hdescent : baseEnd_3087290 < baseStart_3087290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087307 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 1, 4]
def baseStart_3087307 : Nat := 118140960795 + 3087307 * 2 ^ 59
def prefixEnd_3087307 : Nat := 4983230072969 + 3 ^ 40 * 3087307 * 2
def baseEnd_3087307 : Nat := 1056848279326971753909493

theorem tailTrace_3087307 : CollatzResearch.WordTrace tailWord_3087307 prefixEnd_3087307 1056848279326971753909493 := by
  unfold tailWord_3087307
  simp only [CollatzResearch.WordTrace]
  refine ⟨112603337026221483902596175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75068891350814322601730783 112603337026221483902596175)
  ·
    refine ⟨168905005539332225853894263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112603337026221483902596175 168905005539332225853894263)
    ·
      refine ⟨253357508308998338780841395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168905005539332225853894263 253357508308998338780841395)
      ·
        refine ⟨380036262463497508171262093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253357508308998338780841395 380036262463497508171262093)
        ·
          refine ⟨142513598423811565564223285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380036262463497508171262093 142513598423811565564223285)
          ·
            refine ⟨13360649852232334271645933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142513598423811565564223285 13360649852232334271645933)
            ·
              refine ⟨5010243694587125351867225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13360649852232334271645933 5010243694587125351867225)
              ·
                refine ⟨3757682770940344013900419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010243694587125351867225 3757682770940344013900419)
                ·
                  refine ⟨5636524156410516020850629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757682770940344013900419 5636524156410516020850629)
                  ·
                    refine ⟨1056848279326971753909493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5636524156410516020850629 1056848279326971753909493)
                    ·
                      rfl

theorem cell22_3087307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 4].length) (baseStart_3087307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087307 prefixEnd_3087307 := by exact prefixLift 3087307
  have htrace : WordTrace (prefixWord ++ tailWord_3087307) baseStart_3087307 baseEnd_3087307 := by
    simpa [prefixWord, tailWord_3087307, baseEnd_3087307] using wordTrace_append hprefix tailTrace_3087307
  have hstable : (prefixWord ++ tailWord_3087307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087307).length < 2 ^ (prefixWord ++ tailWord_3087307).sum := by decide
  have hdescent : baseEnd_3087307 < baseStart_3087307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087320 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3087320 : Nat := 118140960795 + 3087320 * 2 ^ 59
def prefixEnd_3087320 : Nat := 4983230072969 + 3 ^ 40 * 3087320 * 2
def baseEnd_3087320 : Nat := 1056852729492644053334453

theorem tailTrace_3087320 : CollatzResearch.WordTrace tailWord_3087320 prefixEnd_3087320 1056852729492644053334453 := by
  unfold tailWord_3087320
  simp only [CollatzResearch.WordTrace]
  refine ⟨56301905587587193561409707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75069207450116258081879609 56301905587587193561409707)
  ·
    refine ⟨84452858381380790342114561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56301905587587193561409707 84452858381380790342114561)
    ·
      refine ⟨63339643786035592756585921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84452858381380790342114561 63339643786035592756585921)
      ·
        refine ⟨47504732839526694567439441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63339643786035592756585921 47504732839526694567439441)
        ·
          refine ⟨35628549629645020925579581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47504732839526694567439441 35628549629645020925579581)
          ·
            refine ⟨13360706111116882847092343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35628549629645020925579581 13360706111116882847092343)
            ·
              refine ⟨20041059166675324270638515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13360706111116882847092343 20041059166675324270638515)
              ·
                refine ⟨30061588750012986405957773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20041059166675324270638515 30061588750012986405957773)
                ·
                  refine ⟨11273095781254869902234165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30061588750012986405957773 11273095781254869902234165)
                  ·
                    refine ⟨1056852729492644053334453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11273095781254869902234165 1056852729492644053334453)
                    ·
                      rfl

theorem cell22_3087320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3087320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087320 prefixEnd_3087320 := by exact prefixLift 3087320
  have htrace : WordTrace (prefixWord ++ tailWord_3087320) baseStart_3087320 baseEnd_3087320 := by
    simpa [prefixWord, tailWord_3087320, baseEnd_3087320] using wordTrace_append hprefix tailTrace_3087320
  have hstable : (prefixWord ++ tailWord_3087320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087320).length < 2 ^ (prefixWord ++ tailWord_3087320).sum := by decide
  have hdescent : baseEnd_3087320 < baseStart_3087320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087367 : List Nat := [1, 1, 4, 3, 1, 1, 5, 6]
def baseStart_3087367 : Nat := 118140960795 + 3087367 * 2 ^ 59
def prefixEnd_3087367 : Nat := 4983230072969 + 3 ^ 40 * 3087367 * 2
def baseEnd_3087367 : Nat := 117429868728127955267701

theorem tailTrace_3087367 : CollatzResearch.WordTrace tailWord_3087367 prefixEnd_3087367 117429868728127955267701 := by
  unfold tailWord_3087367
  simp only [CollatzResearch.WordTrace]
  refine ⟨112605525406004114149780355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75070350270669409433186903 112605525406004114149780355)
  ·
    refine ⟨168908288109006171224670533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112605525406004114149780355 168908288109006171224670533)
    ·
      refine ⟨31670304020438657104625725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168908288109006171224670533 31670304020438657104625725)
      ·
        refine ⟨11876364007664496414234647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31670304020438657104625725 11876364007664496414234647)
        ·
          refine ⟨17814546011496744621351971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11876364007664496414234647 17814546011496744621351971)
          ·
            refine ⟨26721819017245116932027957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17814546011496744621351971 26721819017245116932027957)
            ·
              refine ⟨2505170532866729712377621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26721819017245116932027957 2505170532866729712377621)
              ·
                refine ⟨117429868728127955267701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2505170532866729712377621 117429868728127955267701)
                ·
                  rfl

theorem cell22_3087367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 6].length) (baseStart_3087367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087367 prefixEnd_3087367 := by exact prefixLift 3087367
  have htrace : WordTrace (prefixWord ++ tailWord_3087367) baseStart_3087367 baseEnd_3087367 := by
    simpa [prefixWord, tailWord_3087367, baseEnd_3087367] using wordTrace_append hprefix tailTrace_3087367
  have hstable : (prefixWord ++ tailWord_3087367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087367).length < 2 ^ (prefixWord ++ tailWord_3087367).sum := by decide
  have hdescent : baseEnd_3087367 < baseStart_3087367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087388 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_3087388 : Nat := 118140960795 + 3087388 * 2 ^ 59
def prefixEnd_3087388 : Nat := 4983230072969 + 3 ^ 40 * 3087388 * 2
def baseEnd_3087388 : Nat := 1056876007282314542634245

theorem tailTrace_3087388 : CollatzResearch.WordTrace tailWord_3087388 prefixEnd_3087388 1056876007282314542634245 := by
  unfold tailWord_3087388
  simp only [CollatzResearch.WordTrace]
  refine ⟨56303145669464017368147409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75070860892618689824196545 56303145669464017368147409)
  ·
    refine ⟨42227359252098013026110557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56303145669464017368147409 42227359252098013026110557)
    ·
      refine ⟨15835259719536754884791459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42227359252098013026110557 15835259719536754884791459)
      ·
        refine ⟨23752889579305132327187189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15835259719536754884791459 23752889579305132327187189)
        ·
          refine ⟨2226833398059856155673799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23752889579305132327187189 2226833398059856155673799)
          ·
            refine ⟨3340250097089784233510699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226833398059856155673799 3340250097089784233510699)
            ·
              refine ⟨5010375145634676350266049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3340250097089784233510699 5010375145634676350266049)
              ·
                refine ⟨3757781359226007262699537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5010375145634676350266049 3757781359226007262699537)
                ·
                  refine ⟨2818336019419505447024653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757781359226007262699537 2818336019419505447024653)
                  ·
                    refine ⟨1056876007282314542634245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818336019419505447024653 1056876007282314542634245)
                    ·
                      rfl

theorem cell22_3087388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_3087388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087388 prefixEnd_3087388 := by exact prefixLift 3087388
  have htrace : WordTrace (prefixWord ++ tailWord_3087388) baseStart_3087388 baseEnd_3087388 := by
    simpa [prefixWord, tailWord_3087388, baseEnd_3087388] using wordTrace_append hprefix tailTrace_3087388
  have hstable : (prefixWord ++ tailWord_3087388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087388).length < 2 ^ (prefixWord ++ tailWord_3087388).sum := by decide
  have hdescent : baseEnd_3087388 < baseStart_3087388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087440 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_3087440 : Nat := 118140960795 + 3087440 * 2 ^ 59
def prefixEnd_3087440 : Nat := 4983230072969 + 3 ^ 40 * 3087440 * 2
def baseEnd_3087440 : Nat := 352297935981667913444695

theorem tailTrace_3087440 : CollatzResearch.WordTrace tailWord_3087440 prefixEnd_3087440 352297935981667913444695 := by
  unfold tailWord_3087440
  simp only [CollatzResearch.WordTrace]
  refine ⟨56304093967369823808593887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75072125289826431744791849 56304093967369823808593887)
  ·
    refine ⟨84456140951054735712890831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56304093967369823808593887 84456140951054735712890831)
    ·
      refine ⟨126684211426582103569336247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84456140951054735712890831 126684211426582103569336247)
      ·
        refine ⟨190026317139873155354004371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126684211426582103569336247 190026317139873155354004371)
        ·
          refine ⟨285039475709809733031006557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190026317139873155354004371 285039475709809733031006557)
          ·
            refine ⟨106889803391178649886627459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285039475709809733031006557 106889803391178649886627459)
            ·
              refine ⟨160334705086767974829941189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106889803391178649886627459 160334705086767974829941189)
              ·
                refine ⟨30062757203768995280613973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160334705086767974829941189 30062757203768995280613973)
                ·
                  refine ⟨352297935981667913444695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30062757203768995280613973 352297935981667913444695)
                  ·
                    rfl

theorem cell22_3087440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_3087440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087440 prefixEnd_3087440 := by exact prefixLift 3087440
  have htrace : WordTrace (prefixWord ++ tailWord_3087440) baseStart_3087440 baseEnd_3087440 := by
    simpa [prefixWord, tailWord_3087440, baseEnd_3087440] using wordTrace_append hprefix tailTrace_3087440
  have hstable : (prefixWord ++ tailWord_3087440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087440).length < 2 ^ (prefixWord ++ tailWord_3087440).sum := by decide
  have hdescent : baseEnd_3087440 < baseStart_3087440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087457 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 6]
def baseStart_3087457 : Nat := 118140960795 + 3087457 * 2 ^ 59
def prefixEnd_3087457 : Nat := 4983230072969 + 3 ^ 40 * 3087457 * 2
def baseEnd_3087457 : Nat := 352299875797473787553011

theorem tailTrace_3087457 : CollatzResearch.WordTrace tailWord_3087457 prefixEnd_3087457 352299875797473787553011 := by
  unfold tailWord_3087457
  simp only [CollatzResearch.WordTrace]
  refine ⟨112608807975678059520556625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75072538650452039680371083 112608807975678059520556625)
  ·
    refine ⟨84456605981758544640417469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112608807975678059520556625 84456605981758544640417469)
    ·
      refine ⟨31671227243159454240156551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84456605981758544640417469 31671227243159454240156551)
      ·
        refine ⟨47506840864739181360234827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31671227243159454240156551 47506840864739181360234827)
        ·
          refine ⟨71260261297108772040352241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47506840864739181360234827 71260261297108772040352241)
          ·
            refine ⟨53445195972831579030264181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71260261297108772040352241 53445195972831579030264181)
            ·
              refine ⟨5010487122452960534087267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53445195972831579030264181 5010487122452960534087267)
              ·
                refine ⟨7515730683679440801130901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5010487122452960534087267 7515730683679440801130901)
                ·
                  refine ⟨352299875797473787553011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7515730683679440801130901 352299875797473787553011)
                  ·
                    rfl

theorem cell22_3087457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_3087457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087457 prefixEnd_3087457 := by exact prefixLift 3087457
  have htrace : WordTrace (prefixWord ++ tailWord_3087457) baseStart_3087457 baseEnd_3087457 := by
    simpa [prefixWord, tailWord_3087457, baseEnd_3087457] using wordTrace_append hprefix tailTrace_3087457
  have hstable : (prefixWord ++ tailWord_3087457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087457).length < 2 ^ (prefixWord ++ tailWord_3087457).sum := by decide
  have hdescent : baseEnd_3087457 < baseStart_3087457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087472 : List Nat := [2, 1, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_3087472 : Nat := 118140960795 + 3087472 * 2 ^ 59
def prefixEnd_3087472 : Nat := 4983230072969 + 3 ^ 40 * 3087472 * 2
def baseEnd_3087472 : Nat := 1056904762198966323533987

theorem tailTrace_3087472 : CollatzResearch.WordTrace tailWord_3087472 prefixEnd_3087472 1056904762198966323533987 := by
  unfold tailWord_3087472
  simp only [CollatzResearch.WordTrace]
  refine ⟨56304677535311858541176335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75072903380415811388235113 56304677535311858541176335)
  ·
    refine ⟨84457016302967787811764503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56304677535311858541176335 84457016302967787811764503)
    ·
      refine ⟨126685524454451681717646755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84457016302967787811764503 126685524454451681717646755)
      ·
        refine ⟨190028286681677522576470133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126685524454451681717646755 190028286681677522576470133)
        ·
          refine ⟨17815151876407267741544075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 190028286681677522576470133 17815151876407267741544075)
          ·
            refine ⟨26722727814610901612316113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17815151876407267741544075 26722727814610901612316113)
            ·
              refine ⟨20042045860958176209237085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26722727814610901612316113 20042045860958176209237085)
              ·
                refine ⟨7515767197859316078463907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20042045860958176209237085 7515767197859316078463907)
                ·
                  refine ⟨11273650796788974117695861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7515767197859316078463907 11273650796788974117695861)
                  ·
                    refine ⟨1056904762198966323533987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11273650796788974117695861 1056904762198966323533987)
                    ·
                      rfl

theorem cell22_3087472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_3087472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087472 prefixEnd_3087472 := by exact prefixLift 3087472
  have htrace : WordTrace (prefixWord ++ tailWord_3087472) baseStart_3087472 baseEnd_3087472 := by
    simpa [prefixWord, tailWord_3087472, baseEnd_3087472] using wordTrace_append hprefix tailTrace_3087472
  have hstable : (prefixWord ++ tailWord_3087472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087472).length < 2 ^ (prefixWord ++ tailWord_3087472).sum := by decide
  have hdescent : baseEnd_3087472 < baseStart_3087472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087489 : List Nat := [1, 2, 4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3087489 : Nat := 118140960795 + 3087489 * 2 ^ 59
def prefixEnd_3087489 : Nat := 4983230072969 + 3 ^ 40 * 3087489 * 2
def baseEnd_3087489 : Nat := 1056910581646383945858935

theorem tailTrace_3087489 : CollatzResearch.WordTrace tailWord_3087489 prefixEnd_3087489 1056910581646383945858935 := by
  unfold tailWord_3087489
  simp only [CollatzResearch.WordTrace]
  refine ⟨112609975111562128985721521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75073316741041419323814347 112609975111562128985721521)
  ·
    refine ⟨84457481333671596739291141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112609975111562128985721521 84457481333671596739291141)
    ·
      refine ⟨15835777750063424388617089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84457481333671596739291141 15835777750063424388617089)
      ·
        refine ⟨11876833312547568291462817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15835777750063424388617089 11876833312547568291462817)
        ·
          refine ⟨8907624984410676218597113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11876833312547568291462817 8907624984410676218597113)
          ·
            refine ⟨6680718738308007163947835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8907624984410676218597113 6680718738308007163947835)
            ·
              refine ⟨10021078107462010745921753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680718738308007163947835 10021078107462010745921753)
              ·
                refine ⟨7515808580596508059441315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10021078107462010745921753 7515808580596508059441315)
                ·
                  refine ⟨11273712870894762089161973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7515808580596508059441315 11273712870894762089161973)
                  ·
                    refine ⟨1056910581646383945858935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11273712870894762089161973 1056910581646383945858935)
                    ·
                      rfl

theorem cell22_3087489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3087489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087489 prefixEnd_3087489 := by exact prefixLift 3087489
  have htrace : WordTrace (prefixWord ++ tailWord_3087489) baseStart_3087489 baseEnd_3087489 := by
    simpa [prefixWord, tailWord_3087489, baseEnd_3087489] using wordTrace_append hprefix tailTrace_3087489
  have hstable : (prefixWord ++ tailWord_3087489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087489).length < 2 ^ (prefixWord ++ tailWord_3087489).sum := by decide
  have hdescent : baseEnd_3087489 < baseStart_3087489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087502 : List Nat := [4, 1, 1, 3, 2, 11]
def baseStart_3087502 : Nat := 118140960795 + 3087502 * 2 ^ 59
def prefixEnd_3087502 : Nat := 4983230072969 + 3 ^ 40 * 3087502 * 2
def baseEnd_3087502 : Nat := 13048333726074768460295

theorem tailTrace_3087502 : CollatzResearch.WordTrace tailWord_3087502 prefixEnd_3087502 13048333726074768460295 := by
  unfold tailWord_3087502
  simp only [CollatzResearch.WordTrace]
  refine ⟨14076306157564379025743095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75073632840343354803963173 14076306157564379025743095)
  ·
    refine ⟨21114459236346568538614643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14076306157564379025743095 21114459236346568538614643)
    ·
      refine ⟨31671688854519852807921965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21114459236346568538614643 31671688854519852807921965)
      ·
        refine ⟨11876883320444944802970737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31671688854519852807921965 11876883320444944802970737)
        ·
          refine ⟨8907662490333708602228053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11876883320444944802970737 8907662490333708602228053)
          ·
            refine ⟨13048333726074768460295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8907662490333708602228053 13048333726074768460295)
            ·
              rfl

theorem cell22_3087502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 11].length) (baseStart_3087502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087502 prefixEnd_3087502 := by exact prefixLift 3087502
  have htrace : WordTrace (prefixWord ++ tailWord_3087502) baseStart_3087502 baseEnd_3087502 := by
    simpa [prefixWord, tailWord_3087502, baseEnd_3087502] using wordTrace_append hprefix tailTrace_3087502
  have hstable : (prefixWord ++ tailWord_3087502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087502).length < 2 ^ (prefixWord ++ tailWord_3087502).sum := by decide
  have hdescent : baseEnd_3087502 < baseStart_3087502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087506 : List Nat := [3, 2, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3087506 : Nat := 118140960795 + 3087506 * 2 ^ 59
def prefixEnd_3087506 : Nat := 4983230072969 + 3 ^ 40 * 3087506 * 2
def baseEnd_3087506 : Nat := 1056916401093801568183883

theorem tailTrace_3087506 : CollatzResearch.WordTrace tailWord_3087506 prefixEnd_3087506 1056916401093801568183883 := by
  unfold tailWord_3087506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28152648788125135222272593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75073730101667027259393581 28152648788125135222272593)
  ·
    refine ⟨21114486591093851416704445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28152648788125135222272593 21114486591093851416704445)
    ·
      refine ⟨7917932471660194281264167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21114486591093851416704445 7917932471660194281264167)
      ·
        refine ⟨11876898707490291421896251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7917932471660194281264167 11876898707490291421896251)
        ·
          refine ⟨17815348061235437132844377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11876898707490291421896251 17815348061235437132844377)
          ·
            refine ⟨13361511045926577849633283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17815348061235437132844377 13361511045926577849633283)
            ·
              refine ⟨20042266568889866774449925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13361511045926577849633283 20042266568889866774449925)
              ·
                refine ⟨3757924981666850020209361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20042266568889866774449925 3757924981666850020209361)
                ·
                  refine ⟨2818443736250137515157021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757924981666850020209361 2818443736250137515157021)
                  ·
                    refine ⟨1056916401093801568183883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818443736250137515157021 1056916401093801568183883)
                    ·
                      rfl

theorem cell22_3087506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3087506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087506 prefixEnd_3087506 := by exact prefixLift 3087506
  have htrace : WordTrace (prefixWord ++ tailWord_3087506) baseStart_3087506 baseEnd_3087506 := by
    simpa [prefixWord, tailWord_3087506, baseEnd_3087506] using wordTrace_append hprefix tailTrace_3087506
  have hstable : (prefixWord ++ tailWord_3087506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087506).length < 2 ^ (prefixWord ++ tailWord_3087506).sum := by decide
  have hdescent : baseEnd_3087506 < baseStart_3087506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087551 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 1, 3]
def baseStart_3087551 : Nat := 118140960795 + 3087551 * 2 ^ 59
def prefixEnd_3087551 : Nat := 4983230072969 + 3 ^ 40 * 3087551 * 2
def baseEnd_3087551 : Nat := 1056931805513436450808745

theorem tailTrace_3087551 : CollatzResearch.WordTrace tailWord_3087551 prefixEnd_3087551 1056931805513436450808745 := by
  unfold tailWord_3087551
  simp only [CollatzResearch.WordTrace]
  refine ⟨112612236437337513574478507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75074824291558342382985671 112612236437337513574478507)
  ·
    refine ⟨168918354656006270361717761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112612236437337513574478507 168918354656006270361717761)
    ·
      refine ⟨126688765992004702771288321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168918354656006270361717761 126688765992004702771288321)
      ·
        refine ⟨95016574494003527078466241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126688765992004702771288321 95016574494003527078466241)
        ·
          refine ⟨71262430870502645308849681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95016574494003527078466241 71262430870502645308849681)
          ·
            refine ⟨53446823152876983981637261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71262430870502645308849681 53446823152876983981637261)
            ·
              refine ⟨20042558682328868993113973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53446823152876983981637261 20042558682328868993113973)
              ·
                refine ⟨1878989876468331468104435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20042558682328868993113973 1878989876468331468104435)
                ·
                  refine ⟨2818484814702497202156653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878989876468331468104435 2818484814702497202156653)
                  ·
                    refine ⟨1056931805513436450808745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818484814702497202156653 1056931805513436450808745)
                    ·
                      rfl

theorem cell22_3087551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_3087551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087551 prefixEnd_3087551 := by exact prefixLift 3087551
  have htrace : WordTrace (prefixWord ++ tailWord_3087551) baseStart_3087551 baseEnd_3087551 := by
    simpa [prefixWord, tailWord_3087551, baseEnd_3087551] using wordTrace_append hprefix tailTrace_3087551
  have hstable : (prefixWord ++ tailWord_3087551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087551).length < 2 ^ (prefixWord ++ tailWord_3087551).sum := by decide
  have hdescent : baseEnd_3087551 < baseStart_3087551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087602 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_3087602 : Nat := 118140960795 + 3087602 * 2 ^ 59
def prefixEnd_3087602 : Nat := 4983230072969 + 3 ^ 40 * 3087602 * 2
def baseEnd_3087602 : Nat := 1056949263855689317783589

theorem tailTrace_3087602 : CollatzResearch.WordTrace tailWord_3087602 prefixEnd_3087602 1056949263855689317783589 := by
  unfold tailWord_3087602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153524140038187321146265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75076064373435166189723373 28153524140038187321146265)
  ·
    refine ⟨21115143105028640490859699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28153524140038187321146265 21115143105028640490859699)
    ·
      refine ⟨31672714657542960736289549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21115143105028640490859699 31672714657542960736289549)
      ·
        refine ⟨11877267996578610276108581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31672714657542960736289549 11877267996578610276108581)
        ·
          refine ⟨2226987749358489426770359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11877267996578610276108581 2226987749358489426770359)
          ·
            refine ⟨3340481624037734140155539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226987749358489426770359 3340481624037734140155539)
            ·
              refine ⟨5010722436056601210233309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3340481624037734140155539 5010722436056601210233309)
              ·
                refine ⟨1879020913521225453837491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5010722436056601210233309 1879020913521225453837491)
                ·
                  refine ⟨2818531370281838180756237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879020913521225453837491 2818531370281838180756237)
                  ·
                    refine ⟨1056949263855689317783589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818531370281838180756237 1056949263855689317783589)
                    ·
                      rfl

theorem cell22_3087602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_3087602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087602 prefixEnd_3087602 := by exact prefixLift 3087602
  have htrace : WordTrace (prefixWord ++ tailWord_3087602) baseStart_3087602 baseEnd_3087602 := by
    simpa [prefixWord, tailWord_3087602, baseEnd_3087602] using wordTrace_append hprefix tailTrace_3087602
  have hstable : (prefixWord ++ tailWord_3087602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087602).length < 2 ^ (prefixWord ++ tailWord_3087602).sum := by decide
  have hdescent : baseEnd_3087602 < baseStart_3087602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087639 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3087639 : Nat := 118140960795 + 3087639 * 2 ^ 59
def prefixEnd_3087639 : Nat := 4983230072969 + 3 ^ 40 * 3087639 * 2
def baseEnd_3087639 : Nat := 1056961929711833554608475

theorem tailTrace_3087639 : CollatzResearch.WordTrace tailWord_3087639 prefixEnd_3087639 1056961929711833554608475 := by
  unfold tailWord_3087639
  simp only [CollatzResearch.WordTrace]
  refine ⟨112615446061018704603681971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75076964040679136402454647 112615446061018704603681971)
  ·
    refine ⟨168923169091528056905522957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112615446061018704603681971 168923169091528056905522957)
    ·
      refine ⟨63346188409323021339571109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168923169091528056905522957 63346188409323021339571109)
      ·
        refine ⟨11877410326748066501169583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63346188409323021339571109 11877410326748066501169583)
        ·
          refine ⟨17816115490122099751754375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11877410326748066501169583 17816115490122099751754375)
          ·
            refine ⟨26724173235183149627631563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17816115490122099751754375 26724173235183149627631563)
            ·
              refine ⟨40086259852774724441447345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26724173235183149627631563 40086259852774724441447345)
              ·
                refine ⟨30064694889581043331085509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40086259852774724441447345 30064694889581043331085509)
                ·
                  refine ⟨5637130291796445624578533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30064694889581043331085509 5637130291796445624578533)
                  ·
                    refine ⟨1056961929711833554608475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5637130291796445624578533 1056961929711833554608475)
                    ·
                      rfl

theorem cell22_3087639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3087639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087639 prefixEnd_3087639 := by exact prefixLift 3087639
  have htrace : WordTrace (prefixWord ++ tailWord_3087639) baseStart_3087639 baseEnd_3087639 := by
    simpa [prefixWord, tailWord_3087639, baseEnd_3087639] using wordTrace_append hprefix tailTrace_3087639
  have hstable : (prefixWord ++ tailWord_3087639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087639).length < 2 ^ (prefixWord ++ tailWord_3087639).sum := by decide
  have hdescent : baseEnd_3087639 < baseStart_3087639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087656 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3087656 : Nat := 118140960795 + 3087656 * 2 ^ 59
def prefixEnd_3087656 : Nat := 4983230072969 + 3 ^ 40 * 3087656 * 2
def baseEnd_3087656 : Nat := 1056967749159251176933423

theorem tailTrace_3087656 : CollatzResearch.WordTrace tailWord_3087656 prefixEnd_3087656 1056967749159251176933423 := by
  unfold tailWord_3087656
  simp only [CollatzResearch.WordTrace]
  refine ⟨56308033050978558253525411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75077377401304744338033881 56308033050978558253525411)
  ·
    refine ⟨84462049576467837380288117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56308033050978558253525411 84462049576467837380288117)
    ·
      refine ⟨7918317147793859754402011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84462049576467837380288117 7918317147793859754402011)
      ·
        refine ⟨11877475721690789631603017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7918317147793859754402011 11877475721690789631603017)
        ·
          refine ⟨8908106791268092223702263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11877475721690789631603017 8908106791268092223702263)
          ·
            refine ⟨13362160186902138335553395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908106791268092223702263 13362160186902138335553395)
            ·
              refine ⟨20043240280353207503330093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13362160186902138335553395 20043240280353207503330093)
              ·
                refine ⟨7516215105132452813748785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20043240280353207503330093 7516215105132452813748785)
                ·
                  refine ⟨5637161328849339610311589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7516215105132452813748785 5637161328849339610311589)
                  ·
                    refine ⟨1056967749159251176933423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5637161328849339610311589 1056967749159251176933423)
                    ·
                      rfl

theorem cell22_3087656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3087656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087656 prefixEnd_3087656 := by exact prefixLift 3087656
  have htrace : WordTrace (prefixWord ++ tailWord_3087656) baseStart_3087656 baseEnd_3087656 := by
    simpa [prefixWord, tailWord_3087656, baseEnd_3087656] using wordTrace_append hprefix tailTrace_3087656
  have hstable : (prefixWord ++ tailWord_3087656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087656).length < 2 ^ (prefixWord ++ tailWord_3087656).sum := by decide
  have hdescent : baseEnd_3087656 < baseStart_3087656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087677 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 4]
def baseStart_3087677 : Nat := 118140960795 + 3087677 * 2 ^ 59
def prefixEnd_3087677 : Nat := 4983230072969 + 3 ^ 40 * 3087677 * 2
def baseEnd_3087677 : Nat := 352324979296138040719453

theorem tailTrace_3087677 : CollatzResearch.WordTrace tailWord_3087677 prefixEnd_3087677 352324979296138040719453 := by
  unfold tailWord_3087677
  simp only [CollatzResearch.WordTrace]
  refine ⟨112616832034881037093565285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75077888023254024729043523 112616832034881037093565285)
  ·
    refine ⟨21115656006540194455043491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112616832034881037093565285 21115656006540194455043491)
    ·
      refine ⟨31673484009810291682565237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21115656006540194455043491 31673484009810291682565237)
      ·
        refine ⟨2969389125919714845240491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31673484009810291682565237 2969389125919714845240491)
        ·
          refine ⟨4454083688879572267860737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969389125919714845240491 4454083688879572267860737)
          ·
            refine ⟨3340562766659679200895553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4454083688879572267860737 3340562766659679200895553)
            ·
              refine ⟨2505422074994759400671665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340562766659679200895553 2505422074994759400671665)
              ·
                refine ⟨1879066556246069550503749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505422074994759400671665 1879066556246069550503749)
                ·
                  refine ⟨352324979296138040719453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879066556246069550503749 352324979296138040719453)
                  ·
                    rfl

theorem cell22_3087677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 4].length) (baseStart_3087677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087677 prefixEnd_3087677 := by exact prefixLift 3087677
  have htrace : WordTrace (prefixWord ++ tailWord_3087677) baseStart_3087677 baseEnd_3087677 := by
    simpa [prefixWord, tailWord_3087677, baseEnd_3087677] using wordTrace_append hprefix tailTrace_3087677
  have hstable : (prefixWord ++ tailWord_3087677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087677).length < 2 ^ (prefixWord ++ tailWord_3087677).sum := by decide
  have hdescent : baseEnd_3087677 < baseStart_3087677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087699 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 5]
def baseStart_3087699 : Nat := 118140960795 + 3087699 * 2 ^ 59
def prefixEnd_3087699 : Nat := 4983230072969 + 3 ^ 40 * 3087699 * 2
def baseEnd_3087699 : Nat := 352327489646004466036097

theorem tailTrace_3087699 : CollatzResearch.WordTrace tailWord_3087699 prefixEnd_3087699 352327489646004466036097 := by
  unfold tailWord_3087699
  simp only [CollatzResearch.WordTrace]
  refine ⟨112617634440801334850866151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75078422960534223233910767 112617634440801334850866151)
  ·
    refine ⟨168926451661202002276299227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112617634440801334850866151 168926451661202002276299227)
    ·
      refine ⟨253389677491803003414448841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168926451661202002276299227 253389677491803003414448841)
      ·
        refine ⟨190042258118852252560836631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 253389677491803003414448841 190042258118852252560836631)
        ·
          refine ⟨285063387178278378841254947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190042258118852252560836631 285063387178278378841254947)
          ·
            refine ⟨427595080767417568261882421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285063387178278378841254947 427595080767417568261882421)
            ·
              refine ⟨40087038821945397024551477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 427595080767417568261882421 40087038821945397024551477)
              ·
                refine ⟨3758159889557380971051701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40087038821945397024551477 3758159889557380971051701)
                ·
                  refine ⟨352327489646004466036097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3758159889557380971051701 352327489646004466036097)
                  ·
                    rfl

theorem cell22_3087699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 5].length) (baseStart_3087699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087699 prefixEnd_3087699 := by exact prefixLift 3087699
  have htrace : WordTrace (prefixWord ++ tailWord_3087699) baseStart_3087699 baseEnd_3087699 := by
    simpa [prefixWord, tailWord_3087699, baseEnd_3087699] using wordTrace_append hprefix tailTrace_3087699
  have hstable : (prefixWord ++ tailWord_3087699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087699).length < 2 ^ (prefixWord ++ tailWord_3087699).sum := by decide
  have hdescent : baseEnd_3087699 < baseStart_3087699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087776 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_3087776 : Nat := 118140960795 + 3087776 * 2 ^ 59
def prefixEnd_3087776 : Nat := 4983230072969 + 3 ^ 40 * 3087776 * 2
def baseEnd_3087776 : Nat := 1057008827611610863933055

theorem tailTrace_3087776 : CollatzResearch.WordTrace tailWord_3087776 prefixEnd_3087776 1057008827611610863933055 := by
  unfold tailWord_3087776
  simp only [CollatzResearch.WordTrace]
  refine ⟨56310221430761188500709591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75080295241014918000946121 56310221430761188500709591)
  ·
    refine ⟨84465332146141782751064387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56310221430761188500709591 84465332146141782751064387)
    ·
      refine ⟨126697998219212674126596581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84465332146141782751064387 126697998219212674126596581)
      ·
        refine ⟨23755874666102376398736859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126697998219212674126596581 23755874666102376398736859)
        ·
          refine ⟨35633811999153564598105289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23755874666102376398736859 35633811999153564598105289)
          ·
            refine ⟨26725358999365173448578967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35633811999153564598105289 26725358999365173448578967)
            ·
              refine ⟨40088038499047760172868451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26725358999365173448578967 40088038499047760172868451)
              ·
                refine ⟨60132057748571640259302677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40088038499047760172868451 60132057748571640259302677)
                ·
                  refine ⟨2818690206964295637154813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60132057748571640259302677 2818690206964295637154813)
                  ·
                    refine ⟨1057008827611610863933055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818690206964295637154813 1057008827611610863933055)
                    ·
                      rfl

theorem cell22_3087776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_3087776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087776 prefixEnd_3087776 := by exact prefixLift 3087776
  have htrace : WordTrace (prefixWord ++ tailWord_3087776) baseStart_3087776 baseEnd_3087776 := by
    simpa [prefixWord, tailWord_3087776, baseEnd_3087776] using wordTrace_append hprefix tailTrace_3087776
  have hstable : (prefixWord ++ tailWord_3087776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087776).length < 2 ^ (prefixWord ++ tailWord_3087776).sum := by decide
  have hdescent : baseEnd_3087776 < baseStart_3087776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087793 : List Nat := [1, 2, 2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_3087793 : Nat := 118140960795 + 3087793 * 2 ^ 59
def prefixEnd_3087793 : Nat := 4983230072969 + 3 ^ 40 * 3087793 * 2
def baseEnd_3087793 : Nat := 1057014647059028486258003

theorem tailTrace_3087793 : CollatzResearch.WordTrace tailWord_3087793 prefixEnd_3087793 1057014647059028486258003 := by
  unfold tailWord_3087793
  simp only [CollatzResearch.WordTrace]
  refine ⟨112621062902460788904788033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75080708601640525936525355 112621062902460788904788033)
  ·
    refine ⟨84465797176845591678591025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112621062902460788904788033 84465797176845591678591025)
    ·
      refine ⟨63349347882634193758943269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84465797176845591678591025 63349347882634193758943269)
      ·
        refine ⟨11878002727993911329801863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63349347882634193758943269 11878002727993911329801863)
        ·
          refine ⟨17817004091990866994702795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11878002727993911329801863 17817004091990866994702795)
          ·
            refine ⟨26725506137986300492054193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17817004091990866994702795 26725506137986300492054193)
            ·
              refine ⟨20044129603489725369040645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26725506137986300492054193 20044129603489725369040645)
              ·
                refine ⟨3758274300654323506695121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20044129603489725369040645 3758274300654323506695121)
                ·
                  refine ⟨2818705725490742630021341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758274300654323506695121 2818705725490742630021341)
                  ·
                    refine ⟨1057014647059028486258003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818705725490742630021341 1057014647059028486258003)
                    ·
                      rfl

theorem cell22_3087793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_3087793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087793 prefixEnd_3087793 := by exact prefixLift 3087793
  have htrace : WordTrace (prefixWord ++ tailWord_3087793) baseStart_3087793 baseEnd_3087793 := by
    simpa [prefixWord, tailWord_3087793, baseEnd_3087793] using wordTrace_append hprefix tailTrace_3087793
  have hstable : (prefixWord ++ tailWord_3087793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087793).length < 2 ^ (prefixWord ++ tailWord_3087793).sum := by decide
  have hdescent : baseEnd_3087793 < baseStart_3087793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087866 : List Nat := [3, 1, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_3087866 : Nat := 118140960795 + 3087866 * 2 ^ 59
def prefixEnd_3087866 : Nat := 4983230072969 + 3 ^ 40 * 3087866 * 2
def baseEnd_3087866 : Nat := 1057039636450880629182779

theorem tailTrace_3087866 : CollatzResearch.WordTrace tailWord_3087866 prefixEnd_3087866 1057039636450880629182779 := by
  unfold tailWord_3087866
  simp only [CollatzResearch.WordTrace]
  refine ⟨28155931357799080593048863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75082483620797548248130301 28155931357799080593048863)
  ·
    refine ⟨42233897036698620889573295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28155931357799080593048863 42233897036698620889573295)
    ·
      refine ⟨63350845555047931334359943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42233897036698620889573295 63350845555047931334359943)
      ·
        refine ⟨95026268332571897001539915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63350845555047931334359943 95026268332571897001539915)
        ·
          refine ⟨142539402498857845502309873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95026268332571897001539915 142539402498857845502309873)
          ·
            refine ⟨106904551874143384126732405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142539402498857845502309873 106904551874143384126732405)
            ·
              refine ⟨10022301738200942261881163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106904551874143384126732405 10022301738200942261881163)
              ·
                refine ⟨15033452607301413392821745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022301738200942261881163 15033452607301413392821745)
                ·
                  refine ⟨11275089455476060044616309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15033452607301413392821745 11275089455476060044616309)
                  ·
                    refine ⟨1057039636450880629182779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11275089455476060044616309 1057039636450880629182779)
                    ·
                      rfl

theorem cell22_3087866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_3087866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087866 prefixEnd_3087866 := by exact prefixLift 3087866
  have htrace : WordTrace (prefixWord ++ tailWord_3087866) baseStart_3087866 baseEnd_3087866 := by
    simpa [prefixWord, tailWord_3087866, baseEnd_3087866] using wordTrace_append hprefix tailTrace_3087866
  have hstable : (prefixWord ++ tailWord_3087866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087866).length < 2 ^ (prefixWord ++ tailWord_3087866).sum := by decide
  have hdescent : baseEnd_3087866 < baseStart_3087866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087881 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_3087881 : Nat := 118140960795 + 3087881 * 2 ^ 59
def prefixEnd_3087881 : Nat := 4983230072969 + 3 ^ 40 * 3087881 * 2
def baseEnd_3087881 : Nat := 1057044771257425590057733

theorem tailTrace_3087881 : CollatzResearch.WordTrace tailWord_3087881 prefixEnd_3087881 1057044771257425590057733 := by
  unfold tailWord_3087881
  simp only [CollatzResearch.WordTrace]
  refine ⟨112624272526141979933991497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75082848350761319955994331 112624272526141979933991497)
  ·
    refine ⟨84468204394606484950493623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112624272526141979933991497 84468204394606484950493623)
    ·
      refine ⟨126702306591909727425740435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84468204394606484950493623 126702306591909727425740435)
      ·
        refine ⟨190053459887864591138610653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126702306591909727425740435 190053459887864591138610653)
        ·
          refine ⟨71270047457949221676978995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190053459887864591138610653 71270047457949221676978995)
          ·
            refine ⟨106905071186923832515468493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71270047457949221676978995 106905071186923832515468493)
            ·
              refine ⟨40089401695096437193300685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106905071186923832515468493 40089401695096437193300685)
              ·
                refine ⟨15033525635661163947487757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40089401695096437193300685 15033525635661163947487757)
                ·
                  refine ⟨5637572113372936480307909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15033525635661163947487757 5637572113372936480307909)
                  ·
                    refine ⟨1057044771257425590057733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5637572113372936480307909 1057044771257425590057733)
                    ·
                      rfl

theorem cell22_3087881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_3087881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087881 prefixEnd_3087881 := by exact prefixLift 3087881
  have htrace : WordTrace (prefixWord ++ tailWord_3087881) baseStart_3087881 baseEnd_3087881 := by
    simpa [prefixWord, tailWord_3087881, baseEnd_3087881] using wordTrace_append hprefix tailTrace_3087881
  have hstable : (prefixWord ++ tailWord_3087881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087881).length < 2 ^ (prefixWord ++ tailWord_3087881).sum := by decide
  have hdescent : baseEnd_3087881 < baseStart_3087881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087928 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_3087928 : Nat := 118140960795 + 3087928 * 2 ^ 59
def prefixEnd_3087928 : Nat := 4983230072969 + 3 ^ 40 * 3087928 * 2
def baseEnd_3087928 : Nat := 1057060860317933134132589

theorem tailTrace_3087928 : CollatzResearch.WordTrace tailWord_3087928 prefixEnd_3087928 1057060860317933134132589 := by
  unfold tailWord_3087928
  simp only [CollatzResearch.WordTrace]
  refine ⟨56312993378485853480476219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75083991171314471307301625 56312993378485853480476219)
  ·
    refine ⟨84469490067728780220714329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56312993378485853480476219 84469490067728780220714329)
    ·
      refine ⟨63352117550796585165535747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84469490067728780220714329 63352117550796585165535747)
      ·
        refine ⟨95028176326194877748303621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63352117550796585165535747 95028176326194877748303621)
        ·
          refine ⟨17817783061161539577806929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95028176326194877748303621 17817783061161539577806929)
          ·
            refine ⟨13363337295871154683355197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17817783061161539577806929 13363337295871154683355197)
            ·
              refine ⟨5011251485951683006258199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13363337295871154683355197 5011251485951683006258199)
              ·
                refine ⟨7516877228927524509387299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011251485951683006258199 7516877228927524509387299)
                ·
                  refine ⟨11275315843391286764080949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7516877228927524509387299 11275315843391286764080949)
                  ·
                    refine ⟨1057060860317933134132589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11275315843391286764080949 1057060860317933134132589)
                    ·
                      rfl

theorem cell22_3087928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_3087928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087928 prefixEnd_3087928 := by exact prefixLift 3087928
  have htrace : WordTrace (prefixWord ++ tailWord_3087928) baseStart_3087928 baseEnd_3087928 := by
    simpa [prefixWord, tailWord_3087928, baseEnd_3087928] using wordTrace_append hprefix tailTrace_3087928
  have hstable : (prefixWord ++ tailWord_3087928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087928).length < 2 ^ (prefixWord ++ tailWord_3087928).sum := by decide
  have hdescent : baseEnd_3087928 < baseStart_3087928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3087941 : List Nat := [1, 3, 1, 1, 1, 4, 3, 8]
def baseStart_3087941 : Nat := 118140960795 + 3087941 * 2 ^ 59
def prefixEnd_3087941 : Nat := 4983230072969 + 3 ^ 40 * 3087941 * 2
def baseEnd_3087941 : Nat := 117451701164845048173061

theorem tailTrace_3087941 : CollatzResearch.WordTrace tailWord_3087941 prefixEnd_3087941 117451701164845048173061 := by
  unfold tailWord_3087941
  simp only [CollatzResearch.WordTrace]
  refine ⟨112626460905924610181175677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75084307270616406787450451 112626460905924610181175677)
  ·
    refine ⟨42234922839721728817940879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112626460905924610181175677 42234922839721728817940879)
    ·
      refine ⟨63352384259582593226911319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42234922839721728817940879 63352384259582593226911319)
      ·
        refine ⟨95028576389373889840366979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63352384259582593226911319 95028576389373889840366979)
        ·
          refine ⟨142542864584060834760550469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95028576389373889840366979 142542864584060834760550469)
          ·
            refine ⟨26726787109511406517603213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142542864584060834760550469 26726787109511406517603213)
            ·
              refine ⟨10022545166066777444101205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26726787109511406517603213 10022545166066777444101205)
              ·
                refine ⟨117451701164845048173061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10022545166066777444101205 117451701164845048173061)
                ·
                  rfl

theorem cell22_3087941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 8].length) (baseStart_3087941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3087941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3087941 prefixEnd_3087941 := by exact prefixLift 3087941
  have htrace : WordTrace (prefixWord ++ tailWord_3087941) baseStart_3087941 baseEnd_3087941 := by
    simpa [prefixWord, tailWord_3087941, baseEnd_3087941] using wordTrace_append hprefix tailTrace_3087941
  have hstable : (prefixWord ++ tailWord_3087941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3087941).length < 2 ^ (prefixWord ++ tailWord_3087941).sum := by decide
  have hdescent : baseEnd_3087941 < baseStart_3087941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3087941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088024 : List Nat := [2, 1, 2, 4, 1, 2, 4, 2, 1, 3]
def baseStart_3088024 : Nat := 118140960795 + 3088024 * 2 ^ 59
def prefixEnd_3088024 : Nat := 4983230072969 + 3 ^ 40 * 3088024 * 2
def baseEnd_3088024 : Nat := 1057093723079820883732295

theorem tailTrace_3088024 : CollatzResearch.WordTrace tailWord_3088024 prefixEnd_3088024 1057093723079820883732295 := by
  unfold tailWord_3088024
  simp only [CollatzResearch.WordTrace]
  refine ⟨56314744082311957678223563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75086325443082610237631417 56314744082311957678223563)
  ·
    refine ⟨84472116123467936517335345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56314744082311957678223563 84472116123467936517335345)
    ·
      refine ⟨63354087092600952388001509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84472116123467936517335345 63354087092600952388001509)
      ·
        refine ⟨11878891329862678572750283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63354087092600952388001509 11878891329862678572750283)
        ·
          refine ⟨17818336994794017859125425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11878891329862678572750283 17818336994794017859125425)
          ·
            refine ⟨13363752746095513394344069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17818336994794017859125425 13363752746095513394344069)
            ·
              refine ⟨2505703639892908761439513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13363752746095513394344069 2505703639892908761439513)
              ·
                refine ⟨1879277729919681571079635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2505703639892908761439513 1879277729919681571079635)
                ·
                  refine ⟨2818916594879522356619453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879277729919681571079635 2818916594879522356619453)
                  ·
                    refine ⟨1057093723079820883732295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818916594879522356619453 1057093723079820883732295)
                    ·
                      rfl

theorem cell22_3088024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_3088024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088024 prefixEnd_3088024 := by exact prefixLift 3088024
  have htrace : WordTrace (prefixWord ++ tailWord_3088024) baseStart_3088024 baseEnd_3088024 := by
    simpa [prefixWord, tailWord_3088024, baseEnd_3088024] using wordTrace_append hprefix tailTrace_3088024
  have hstable : (prefixWord ++ tailWord_3088024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088024).length < 2 ^ (prefixWord ++ tailWord_3088024).sum := by decide
  have hdescent : baseEnd_3088024 < baseStart_3088024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088063 : List Nat := [1, 1, 2, 2, 2, 3, 1, 4, 1, 5]
def baseStart_3088063 : Nat := 118140960795 + 3088063 * 2 ^ 59
def prefixEnd_3088063 : Nat := 4983230072969 + 3 ^ 40 * 3088063 * 2
def baseEnd_3088063 : Nat := 1057107073576837782007175

theorem tailTrace_3088063 : CollatzResearch.WordTrace tailWord_3088063 prefixEnd_3088063 1057107073576837782007175 := by
  unfold tailWord_3088063
  simp only [CollatzResearch.WordTrace]
  refine ⟨112630910611482625017116843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75087273740988416678077895 112630910611482625017116843)
  ·
    refine ⟨168946365917223937525675265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112630910611482625017116843 168946365917223937525675265)
    ·
      refine ⟨126709774437917953144256449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168946365917223937525675265 126709774437917953144256449)
      ·
        refine ⟨95032330828438464858192337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126709774437917953144256449 95032330828438464858192337)
        ·
          refine ⟨71274248121328848643644253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95032330828438464858192337 71274248121328848643644253)
          ·
            refine ⟨26727843045498318241366595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71274248121328848643644253 26727843045498318241366595)
            ·
              refine ⟨40091764568247477362049893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26727843045498318241366595 40091764568247477362049893)
              ·
                refine ⟨7517205856546402005384355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40091764568247477362049893 7517205856546402005384355)
                ·
                  refine ⟨11275808784819603008076533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517205856546402005384355 11275808784819603008076533)
                  ·
                    refine ⟨1057107073576837782007175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11275808784819603008076533 1057107073576837782007175)
                    ·
                      rfl

theorem cell22_3088063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_3088063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088063 prefixEnd_3088063 := by exact prefixLift 3088063
  have htrace : WordTrace (prefixWord ++ tailWord_3088063) baseStart_3088063 baseEnd_3088063 := by
    simpa [prefixWord, tailWord_3088063, baseEnd_3088063] using wordTrace_append hprefix tailTrace_3088063
  have hstable : (prefixWord ++ tailWord_3088063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088063).length < 2 ^ (prefixWord ++ tailWord_3088063).sum := by decide
  have hdescent : baseEnd_3088063 < baseStart_3088063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088080 : List Nat := [2, 1, 1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_3088080 : Nat := 118140960795 + 3088080 * 2 ^ 59
def prefixEnd_3088080 : Nat := 4983230072969 + 3 ^ 40 * 3088080 * 2
def baseEnd_3088080 : Nat := 1057112893024255404332123

theorem tailTrace_3088080 : CollatzResearch.WordTrace tailWord_3088080 prefixEnd_3088080 1057112893024255404332123 := by
  unfold tailWord_3088080
  simp only [CollatzResearch.WordTrace]
  refine ⟨56315765326210518460242847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75087687101614024613657129 56315765326210518460242847)
  ·
    refine ⟨84473647989315777690364271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56315765326210518460242847 84473647989315777690364271)
    ·
      refine ⟨126710471983973666535546407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84473647989315777690364271 126710471983973666535546407)
      ·
        refine ⟨190065707975960499803319611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126710471983973666535546407 190065707975960499803319611)
        ·
          refine ⟨285098561963940749704979417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190065707975960499803319611 285098561963940749704979417)
          ·
            refine ⟨213823921472955562278734563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285098561963940749704979417 213823921472955562278734563)
            ·
              refine ⟨320735882209433343418101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213823921472955562278734563 320735882209433343418101845)
              ·
                refine ⟨3758623619641796993180881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 320735882209433343418101845 3758623619641796993180881)
                ·
                  refine ⟨2818967714731347744885661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758623619641796993180881 2818967714731347744885661)
                  ·
                    refine ⟨1057112893024255404332123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2818967714731347744885661 1057112893024255404332123)
                    ·
                      rfl

theorem cell22_3088080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_3088080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088080 prefixEnd_3088080 := by exact prefixLift 3088080
  have htrace : WordTrace (prefixWord ++ tailWord_3088080) baseStart_3088080 baseEnd_3088080 := by
    simpa [prefixWord, tailWord_3088080, baseEnd_3088080] using wordTrace_append hprefix tailTrace_3088080
  have hstable : (prefixWord ++ tailWord_3088080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088080).length < 2 ^ (prefixWord ++ tailWord_3088080).sum := by decide
  have hdescent : baseEnd_3088080 < baseStart_3088080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088082 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_3088082 : Nat := 118140960795 + 3088082 * 2 ^ 59
def prefixEnd_3088082 : Nat := 4983230072969 + 3 ^ 40 * 3088082 * 2
def baseEnd_3088082 : Nat := 352371192555042688594039

theorem tailTrace_3088082 : CollatzResearch.WordTrace tailWord_3088082 prefixEnd_3088082 352371192555042688594039 := by
  unfold tailWord_3088082
  simp only [CollatzResearch.WordTrace]
  refine ⟨28157900899603447815514625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75087735732275860841372333 28157900899603447815514625)
  ·
    refine ⟨21118425674702585861635969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28157900899603447815514625 21118425674702585861635969)
    ·
      refine ⟨15838819256026939396226977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21118425674702585861635969 15838819256026939396226977)
      ·
        refine ⟨11879114442020204547170233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15838819256026939396226977 11879114442020204547170233)
        ·
          refine ⟨8909335831515153410377675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11879114442020204547170233 8909335831515153410377675)
          ·
            refine ⟨13364003747272730115566513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8909335831515153410377675 13364003747272730115566513)
            ·
              refine ⟨10023002810454547586674885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13364003747272730115566513 10023002810454547586674885)
              ·
                refine ⟨1879313026960227672501541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10023002810454547586674885 1879313026960227672501541)
                ·
                  refine ⟨352371192555042688594039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879313026960227672501541 352371192555042688594039)
                  ·
                    rfl

theorem cell22_3088082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_3088082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088082 prefixEnd_3088082 := by exact prefixLift 3088082
  have htrace : WordTrace (prefixWord ++ tailWord_3088082) baseStart_3088082 baseEnd_3088082 := by
    simpa [prefixWord, tailWord_3088082, baseEnd_3088082] using wordTrace_append hprefix tailTrace_3088082
  have hstable : (prefixWord ++ tailWord_3088082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088082).length < 2 ^ (prefixWord ++ tailWord_3088082).sum := by decide
  have hdescent : baseEnd_3088082 < baseStart_3088082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088097 : List Nat := [1, 2, 3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_3088097 : Nat := 118140960795 + 3088097 * 2 ^ 59
def prefixEnd_3088097 : Nat := 4983230072969 + 3 ^ 40 * 3088097 * 2
def baseEnd_3088097 : Nat := 1057118712471673026657071

theorem tailTrace_3088097 : CollatzResearch.WordTrace tailWord_3088097 prefixEnd_3088097 1057118712471673026657071 := by
  unfold tailWord_3088097
  simp only [CollatzResearch.WordTrace]
  refine ⟨112632150693359448823854545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75088100462239632549236363 112632150693359448823854545)
  ·
    refine ⟨84474113020019586617890909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112632150693359448823854545 84474113020019586617890909)
    ·
      refine ⟨31677792382507344981709091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84474113020019586617890909 31677792382507344981709091)
      ·
        refine ⟨47516688573761017472563637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31677792382507344981709091 47516688573761017472563637)
        ·
          refine ⟨4454689553790095388052841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47516688573761017472563637 4454689553790095388052841)
          ·
            refine ⟨3341017165342571541039631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4454689553790095388052841 3341017165342571541039631)
            ·
              refine ⟨5011525748013857311559447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341017165342571541039631 5011525748013857311559447)
              ·
                refine ⟨7517288622020785967339171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011525748013857311559447 7517288622020785967339171)
                ·
                  refine ⟨11275932933031178951008757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517288622020785967339171 11275932933031178951008757)
                  ·
                    refine ⟨1057118712471673026657071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11275932933031178951008757 1057118712471673026657071)
                    ·
                      rfl

theorem cell22_3088097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_3088097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088097 prefixEnd_3088097 := by exact prefixLift 3088097
  have htrace : WordTrace (prefixWord ++ tailWord_3088097) baseStart_3088097 baseEnd_3088097 := by
    simpa [prefixWord, tailWord_3088097, baseEnd_3088097] using wordTrace_append hprefix tailTrace_3088097
  have hstable : (prefixWord ++ tailWord_3088097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088097).length < 2 ^ (prefixWord ++ tailWord_3088097).sum := by decide
  have hdescent : baseEnd_3088097 < baseStart_3088097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088116 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3088116 : Nat := 118140960795 + 3088116 * 2 ^ 59
def prefixEnd_3088116 : Nat := 4983230072969 + 3 ^ 40 * 3088116 * 2
def baseEnd_3088116 : Nat := 352375072186654436810671

theorem tailTrace_3088116 : CollatzResearch.WordTrace tailWord_3088116 prefixEnd_3088116 352375072186654436810671 := by
  unfold tailWord_3088116
  simp only [CollatzResearch.WordTrace]
  refine ⟨56316421840145307534398101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75088562453527076712530801 56316421840145307534398101)
  ·
    refine ⟨2639832273756811290674911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56316421840145307534398101 2639832273756811290674911)
    ·
      refine ⟨3959748410635216936012367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2639832273756811290674911 3959748410635216936012367)
      ·
        refine ⟨5939622615952825404018551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3959748410635216936012367 5939622615952825404018551)
        ·
          refine ⟨8909433923929238106027827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5939622615952825404018551 8909433923929238106027827)
          ·
            refine ⟨13364150885893857159041741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8909433923929238106027827 13364150885893857159041741)
            ·
              refine ⟨5011556582210196434640653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13364150885893857159041741 5011556582210196434640653)
              ·
                refine ⟨1879333718328823662990245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5011556582210196434640653 1879333718328823662990245)
                ·
                  refine ⟨352375072186654436810671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879333718328823662990245 352375072186654436810671)
                  ·
                    rfl

theorem cell22_3088116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3088116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088116 prefixEnd_3088116 := by exact prefixLift 3088116
  have htrace : WordTrace (prefixWord ++ tailWord_3088116) baseStart_3088116 baseEnd_3088116 := by
    simpa [prefixWord, tailWord_3088116, baseEnd_3088116] using wordTrace_append hprefix tailTrace_3088116
  have hstable : (prefixWord ++ tailWord_3088116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088116).length < 2 ^ (prefixWord ++ tailWord_3088116).sum := by decide
  have hdescent : baseEnd_3088116 < baseStart_3088116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088142 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_3088142 : Nat := 118140960795 + 3088142 * 2 ^ 59
def prefixEnd_3088142 : Nat := 4983230072969 + 3 ^ 40 * 3088142 * 2
def baseEnd_3088142 : Nat := 1057134116891307909281933

theorem tailTrace_3088142 : CollatzResearch.WordTrace tailWord_3088142 prefixEnd_3088142 1057134116891307909281933 := by
  unfold tailWord_3088142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14079223997274552688655335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75089194652130947672828453 14079223997274552688655335)
  ·
    refine ⟨21118835995911829032983003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14079223997274552688655335 21118835995911829032983003)
    ·
      refine ⟨31678253993867743549474505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21118835995911829032983003 31678253993867743549474505)
      ·
        refine ⟨23758690495400807662105879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31678253993867743549474505 23758690495400807662105879)
        ·
          refine ⟨35638035743101211493158819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23758690495400807662105879 35638035743101211493158819)
          ·
            refine ⟨53457053614651817239738229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35638035743101211493158819 53457053614651817239738229)
            ·
              refine ⟨5011598776373607866225459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53457053614651817239738229 5011598776373607866225459)
              ·
                refine ⟨7517398164560411799338189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011598776373607866225459 7517398164560411799338189)
                ·
                  refine ⟨2819024311710154424751821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7517398164560411799338189 2819024311710154424751821)
                  ·
                    refine ⟨1057134116891307909281933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819024311710154424751821 1057134116891307909281933)
                    ·
                      rfl

theorem cell22_3088142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_3088142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088142 prefixEnd_3088142 := by exact prefixLift 3088142
  have htrace : WordTrace (prefixWord ++ tailWord_3088142) baseStart_3088142 baseEnd_3088142 := by
    simpa [prefixWord, tailWord_3088142, baseEnd_3088142] using wordTrace_append hprefix tailTrace_3088142
  have hstable : (prefixWord ++ tailWord_3088142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088142).length < 2 ^ (prefixWord ++ tailWord_3088142).sum := by decide
  have hdescent : baseEnd_3088142 < baseStart_3088142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088148 : List Nat := [2, 4, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3088148 : Nat := 118140960795 + 3088148 * 2 ^ 59
def prefixEnd_3088148 : Nat := 4983230072969 + 3 ^ 40 * 3088148 * 2
def baseEnd_3088148 : Nat := 1057136170813925893631915

theorem tailTrace_3088148 : CollatzResearch.WordTrace tailWord_3088148 prefixEnd_3088148 1057136170813925893631915 := by
  unfold tailWord_3088148
  simp only [CollatzResearch.WordTrace]
  refine ⟨56317005408087342266980549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75089340544116456355974065 56317005408087342266980549)
  ·
    refine ⟨10559438514016376675058853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56317005408087342266980549 10559438514016376675058853)
    ·
      refine ⟨1979894721378070626573535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10559438514016376675058853 1979894721378070626573535)
      ·
        refine ⟨2969842082067105939860303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979894721378070626573535 2969842082067105939860303)
        ·
          refine ⟨4454763123100658909790455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969842082067105939860303 4454763123100658909790455)
          ·
            refine ⟨6682144684650988364685683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454763123100658909790455 6682144684650988364685683)
            ·
              refine ⟨10023217026976482547028525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682144684650988364685683 10023217026976482547028525)
              ·
                refine ⟨3758706385116180955135697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10023217026976482547028525 3758706385116180955135697)
                ·
                  refine ⟨2819029788837135716351773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3758706385116180955135697 2819029788837135716351773)
                  ·
                    refine ⟨1057136170813925893631915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819029788837135716351773 1057136170813925893631915)
                    ·
                      rfl

theorem cell22_3088148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3088148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088148 prefixEnd_3088148 := by exact prefixLift 3088148
  have htrace : WordTrace (prefixWord ++ tailWord_3088148) baseStart_3088148 baseEnd_3088148 := by
    simpa [prefixWord, tailWord_3088148, baseEnd_3088148] using wordTrace_append hprefix tailTrace_3088148
  have hstable : (prefixWord ++ tailWord_3088148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088148).length < 2 ^ (prefixWord ++ tailWord_3088148).sum := by decide
  have hdescent : baseEnd_3088148 < baseStart_3088148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088153 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_3088153 : Nat := 118140960795 + 3088153 * 2 ^ 59
def prefixEnd_3088153 : Nat := 4983230072969 + 3 ^ 40 * 3088153 * 2
def baseEnd_3088153 : Nat := 1057137882416107547256899

theorem tailTrace_3088153 : CollatzResearch.WordTrace tailWord_3088153 prefixEnd_3088153 1057137882416107547256899 := by
  unfold tailWord_3088153
  simp only [CollatzResearch.WordTrace]
  refine ⟨112634193181156570387893113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75089462120771046925262075 112634193181156570387893113)
  ·
    refine ⟨84475644885867427790919835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112634193181156570387893113 84475644885867427790919835)
    ·
      refine ⟨126713467328801141686379753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84475644885867427790919835 126713467328801141686379753)
      ·
        refine ⟨95035100496600856264784815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126713467328801141686379753 95035100496600856264784815)
        ·
          refine ⟨142552650744901284397177223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95035100496600856264784815 142552650744901284397177223)
          ·
            refine ⟨213828976117351926595765835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142552650744901284397177223 213828976117351926595765835)
            ·
              refine ⟨320743464176027889893648753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213828976117351926595765835 320743464176027889893648753)
              ·
                refine ⟨240557598132020917420236565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320743464176027889893648753 240557598132020917420236565)
                ·
                  refine ⟨11276137412438480504073589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 240557598132020917420236565 11276137412438480504073589)
                  ·
                    refine ⟨1057137882416107547256899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11276137412438480504073589 1057137882416107547256899)
                    ·
                      rfl

theorem cell22_3088153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_3088153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088153 prefixEnd_3088153 := by exact prefixLift 3088153
  have htrace : WordTrace (prefixWord ++ tailWord_3088153) baseStart_3088153 baseEnd_3088153 := by
    simpa [prefixWord, tailWord_3088153, baseEnd_3088153] using wordTrace_append hprefix tailTrace_3088153
  have hstable : (prefixWord ++ tailWord_3088153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088153).length < 2 ^ (prefixWord ++ tailWord_3088153).sum := by decide
  have hdescent : baseEnd_3088153 < baseStart_3088153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088183 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 10]
def baseStart_3088183 : Nat := 118140960795 + 3088183 * 2 ^ 59
def prefixEnd_3088183 : Nat := 4983230072969 + 3 ^ 40 * 3088183 * 2
def baseEnd_3088183 : Nat := 352382717343065823002269

theorem tailTrace_3088183 : CollatzResearch.WordTrace tailWord_3088183 prefixEnd_3088183 352382717343065823002269 := by
  unfold tailWord_3088183
  simp only [CollatzResearch.WordTrace]
  refine ⟨112635287371047885511485203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75090191580698590340990135 112635287371047885511485203)
  ·
    refine ⟨168952931056571828267227805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112635287371047885511485203 168952931056571828267227805)
    ·
      refine ⟨63357349146214435600210427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168952931056571828267227805 63357349146214435600210427)
      ·
        refine ⟨95036023719321653400315641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63357349146214435600210427 95036023719321653400315641)
        ·
          refine ⟨71277017789491240050236731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95036023719321653400315641 71277017789491240050236731)
          ·
            refine ⟨106915526684236860075355097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71277017789491240050236731 106915526684236860075355097)
            ·
              refine ⟨80186645013177645056516323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106915526684236860075355097 80186645013177645056516323)
              ·
                refine ⟨120279967519766467584774485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80186645013177645056516323 120279967519766467584774485)
                ·
                  refine ⟨352382717343065823002269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 120279967519766467584774485 352382717343065823002269)
                  ·
                    rfl

theorem cell22_3088183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 10].length) (baseStart_3088183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088183 prefixEnd_3088183 := by exact prefixLift 3088183
  have htrace : WordTrace (prefixWord ++ tailWord_3088183) baseStart_3088183 baseEnd_3088183 := by
    simpa [prefixWord, tailWord_3088183, baseEnd_3088183] using wordTrace_append hprefix tailTrace_3088183
  have hstable : (prefixWord ++ tailWord_3088183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088183).length < 2 ^ (prefixWord ++ tailWord_3088183).sum := by decide
  have hdescent : baseEnd_3088183 < baseStart_3088183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088232 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3088232 : Nat := 118140960795 + 3088232 * 2 ^ 59
def prefixEnd_3088232 : Nat := 4983230072969 + 3 ^ 40 * 3088232 * 2
def baseEnd_3088232 : Nat := 1057164925730577674531657

theorem tailTrace_3088232 : CollatzResearch.WordTrace tailWord_3088232 prefixEnd_3088232 1057164925730577674531657 := by
  unfold tailWord_3088232
  simp only [CollatzResearch.WordTrace]
  refine ⟨56318537273935183440009475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75091383031913577920012633 56318537273935183440009475)
  ·
    refine ⟨84477805910902775160014213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56318537273935183440009475 84477805910902775160014213)
    ·
      refine ⟨15839588608294270342502665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84477805910902775160014213 15839588608294270342502665)
      ·
        refine ⟨11879691456220702756876999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15839588608294270342502665 11879691456220702756876999)
        ·
          refine ⟨17819537184331054135315499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11879691456220702756876999 17819537184331054135315499)
          ·
            refine ⟨26729305776496581202973249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17819537184331054135315499 26729305776496581202973249)
            ·
              refine ⟨20046979332372435902229937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26729305776496581202973249 20046979332372435902229937)
              ·
                refine ⟨15035234499279326926672453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20046979332372435902229937 15035234499279326926672453)
                ·
                  refine ⟨2819106468614873798751085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15035234499279326926672453 2819106468614873798751085)
                  ·
                    refine ⟨1057164925730577674531657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819106468614873798751085 1057164925730577674531657)
                    ·
                      rfl

theorem cell22_3088232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3088232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088232 prefixEnd_3088232 := by exact prefixLift 3088232
  have htrace : WordTrace (prefixWord ++ tailWord_3088232) baseStart_3088232 baseEnd_3088232 := by
    simpa [prefixWord, tailWord_3088232, baseEnd_3088232] using wordTrace_append hprefix tailTrace_3088232
  have hstable : (prefixWord ++ tailWord_3088232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088232).length < 2 ^ (prefixWord ++ tailWord_3088232).sum := by decide
  have hdescent : baseEnd_3088232 < baseStart_3088232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088245 : List Nat := [1, 3, 4, 1, 1, 1, 11]
def baseStart_3088245 : Nat := 118140960795 + 3088245 * 2 ^ 59
def prefixEnd_3088245 : Nat := 4983230072969 + 3 ^ 40 * 3088245 * 2
def baseEnd_3088245 : Nat := 39154421329490739776171

theorem tailTrace_3088245 : CollatzResearch.WordTrace tailWord_3088245 prefixEnd_3088245 39154421329490739776171 := by
  unfold tailWord_3088245
  simp only [CollatzResearch.WordTrace]
  refine ⟨112637548696823270100242189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75091699131215513400161459 112637548696823270100242189)
  ·
    refine ⟨42239080761308726287590821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112637548696823270100242189 42239080761308726287590821)
    ·
      refine ⟨7919827642745386178923279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42239080761308726287590821 7919827642745386178923279)
      ·
        refine ⟨11879741464118079268384919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7919827642745386178923279 11879741464118079268384919)
        ·
          refine ⟨17819612196177118902577379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11879741464118079268384919 17819612196177118902577379)
          ·
            refine ⟨26729418294265678353866069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17819612196177118902577379 26729418294265678353866069)
            ·
              refine ⟨39154421329490739776171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26729418294265678353866069 39154421329490739776171)
              ·
                rfl

theorem cell22_3088245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 11].length) (baseStart_3088245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088245 prefixEnd_3088245 := by exact prefixLift 3088245
  have htrace : WordTrace (prefixWord ++ tailWord_3088245) baseStart_3088245 baseEnd_3088245 := by
    simpa [prefixWord, tailWord_3088245, baseEnd_3088245] using wordTrace_append hprefix tailTrace_3088245
  have hstable : (prefixWord ++ tailWord_3088245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088245).length < 2 ^ (prefixWord ++ tailWord_3088245).sum := by decide
  have hdescent : baseEnd_3088245 < baseStart_3088245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088266 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 1, 5]
def baseStart_3088266 : Nat := 118140960795 + 3088266 * 2 ^ 59
def prefixEnd_3088266 : Nat := 4983230072969 + 3 ^ 40 * 3088266 * 2
def baseEnd_3088266 : Nat := 1057176564625412919181553

theorem tailTrace_3088266 : CollatzResearch.WordTrace tailWord_3088266 prefixEnd_3088266 1057176564625412919181553 := by
  unfold tailWord_3088266
  simp only [CollatzResearch.WordTrace]
  refine ⟨28159578657436797671689163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75092209753164793791171101 28159578657436797671689163)
  ·
    refine ⟨42239367986155196507533745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28159578657436797671689163 42239367986155196507533745)
    ·
      refine ⟨31679525989616397380650309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42239367986155196507533745 31679525989616397380650309)
      ·
        refine ⟨5939911123053074508871933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31679525989616397380650309 5939911123053074508871933)
        ·
          refine ⟨2227466671144902940826975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5939911123053074508871933 2227466671144902940826975)
          ·
            refine ⟨3341200006717354411240463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227466671144902940826975 3341200006717354411240463)
            ·
              refine ⟨5011800010076031616860695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341200006717354411240463 5011800010076031616860695)
              ·
                refine ⟨7517700015114047425291043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011800010076031616860695 7517700015114047425291043)
                ·
                  refine ⟨11276550022671071137936565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517700015114047425291043 11276550022671071137936565)
                  ·
                    refine ⟨1057176564625412919181553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11276550022671071137936565 1057176564625412919181553)
                    ·
                      rfl

theorem cell22_3088266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_3088266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088266 prefixEnd_3088266 := by exact prefixLift 3088266
  have htrace : WordTrace (prefixWord ++ tailWord_3088266) baseStart_3088266 baseEnd_3088266 := by
    simpa [prefixWord, tailWord_3088266, baseEnd_3088266] using wordTrace_append hprefix tailTrace_3088266
  have hstable : (prefixWord ++ tailWord_3088266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088266).length < 2 ^ (prefixWord ++ tailWord_3088266).sum := by decide
  have hdescent : baseEnd_3088266 < baseStart_3088266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088277 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 3, 3]
def baseStart_3088277 : Nat := 118140960795 + 3088277 * 2 ^ 59
def prefixEnd_3088277 : Nat := 4983230072969 + 3 ^ 40 * 3088277 * 2
def baseEnd_3088277 : Nat := 1057180330150212557156519

theorem tailTrace_3088277 : CollatzResearch.WordTrace tailWord_3088277 prefixEnd_3088277 1057180330150212557156519 := by
  unfold tailWord_3088277
  simp only [CollatzResearch.WordTrace]
  refine ⟨112638715832707339565407085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75092477221804893043604723 112638715832707339565407085)
  ·
    refine ⟨42239518437265252337027657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112638715832707339565407085 42239518437265252337027657)
    ·
      refine ⟨31679638827948939252770743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42239518437265252337027657 31679638827948939252770743)
      ·
        refine ⟨47519458241923408879156115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31679638827948939252770743 47519458241923408879156115)
        ·
          refine ⟨71279187362885113318734173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47519458241923408879156115 71279187362885113318734173)
          ·
            refine ⟨26729695261081917494525315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71279187362885113318734173 26729695261081917494525315)
            ·
              refine ⟨40094542891622876241787973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26729695261081917494525315 40094542891622876241787973)
              ·
                refine ⟨7517726792179289295335245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40094542891622876241787973 7517726792179289295335245)
                ·
                  refine ⟨2819147547067233485750717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7517726792179289295335245 2819147547067233485750717)
                  ·
                    refine ⟨1057180330150212557156519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819147547067233485750717 1057180330150212557156519)
                    ·
                      rfl

theorem cell22_3088277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_3088277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088277 prefixEnd_3088277 := by exact prefixLift 3088277
  have htrace : WordTrace (prefixWord ++ tailWord_3088277) baseStart_3088277 baseEnd_3088277 := by
    simpa [prefixWord, tailWord_3088277, baseEnd_3088277] using wordTrace_append hprefix tailTrace_3088277
  have hstable : (prefixWord ++ tailWord_3088277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088277).length < 2 ^ (prefixWord ++ tailWord_3088277).sum := by decide
  have hdescent : baseEnd_3088277 < baseStart_3088277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088296 : List Nat := [2, 1, 6, 2, 2, 1, 8]
def baseStart_3088296 : Nat := 118140960795 + 3088296 * 2 ^ 59
def prefixEnd_3088296 : Nat := 4983230072969 + 3 ^ 40 * 3088296 * 2
def baseEnd_3088296 : Nat := 39155067934759364478943

theorem tailTrace_3088296 : CollatzResearch.WordTrace tailWord_3088296 prefixEnd_3088296 39155067934759364478943 := by
  unfold tailWord_3088296
  simp only [CollatzResearch.WordTrace]
  refine ⟨56319704409819252905174371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75092939213092337206899161 56319704409819252905174371)
  ·
    refine ⟨84479556614728879357761557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56319704409819252905174371 84479556614728879357761557)
    ·
      refine ⟨3959979216315416219895073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 84479556614728879357761557 3959979216315416219895073)
      ·
        refine ⟨2969984412236562164921305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3959979216315416219895073 2969984412236562164921305)
        ·
          refine ⟨2227488309177421623690979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2969984412236562164921305 2227488309177421623690979)
          ·
            refine ⟨3341232463766132435536469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227488309177421623690979 3341232463766132435536469)
            ·
              refine ⟨39155067934759364478943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3341232463766132435536469 39155067934759364478943)
              ·
                rfl

theorem cell22_3088296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 8].length) (baseStart_3088296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088296 prefixEnd_3088296 := by exact prefixLift 3088296
  have htrace : WordTrace (prefixWord ++ tailWord_3088296) baseStart_3088296 baseEnd_3088296 := by
    simpa [prefixWord, tailWord_3088296, baseEnd_3088296] using wordTrace_append hprefix tailTrace_3088296
  have hstable : (prefixWord ++ tailWord_3088296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088296).length < 2 ^ (prefixWord ++ tailWord_3088296).sum := by decide
  have hdescent : baseEnd_3088296 < baseStart_3088296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088335 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 8]
def baseStart_3088335 : Nat := 118140960795 + 3088335 * 2 ^ 59
def prefixEnd_3088335 : Nat := 4983230072969 + 3 ^ 40 * 3088335 * 2
def baseEnd_3088335 : Nat := 352400061578506579735447

theorem tailTrace_3088335 : CollatzResearch.WordTrace tailWord_3088335 prefixEnd_3088335 352400061578506579735447 := by
  unfold tailWord_3088335
  simp only [CollatzResearch.WordTrace]
  refine ⟨112640831266497215471018459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75093887510998143647345639 112640831266497215471018459)
  ·
    refine ⟨168961246899745823206527689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112640831266497215471018459 168961246899745823206527689)
    ·
      refine ⟨126720935174809367404895767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168961246899745823206527689 126720935174809367404895767)
      ·
        refine ⟨190081402762214051107343651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126720935174809367404895767 190081402762214051107343651)
        ·
          refine ⟨285122104143321076661015477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190081402762214051107343651 285122104143321076661015477)
          ·
            refine ⟨26730197263436350936970201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 285122104143321076661015477 26730197263436350936970201)
            ·
              refine ⟨20047647947577263202727651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26730197263436350936970201 20047647947577263202727651)
              ·
                refine ⟨30071471921365894804091477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20047647947577263202727651 30071471921365894804091477)
                ·
                  refine ⟨352400061578506579735447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30071471921365894804091477 352400061578506579735447)
                  ·
                    rfl

theorem cell22_3088335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 8].length) (baseStart_3088335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088335 prefixEnd_3088335 := by exact prefixLift 3088335
  have htrace : WordTrace (prefixWord ++ tailWord_3088335) baseStart_3088335 baseEnd_3088335 := by
    simpa [prefixWord, tailWord_3088335, baseEnd_3088335] using wordTrace_append hprefix tailTrace_3088335
  have hstable : (prefixWord ++ tailWord_3088335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088335).length < 2 ^ (prefixWord ++ tailWord_3088335).sum := by decide
  have hdescent : baseEnd_3088335 < baseStart_3088335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088337 : List Nat := [1, 2, 2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_3088337 : Nat := 118140960795 + 3088337 * 2 ^ 59
def prefixEnd_3088337 : Nat := 4983230072969 + 3 ^ 40 * 3088337 * 2
def baseEnd_3088337 : Nat := 1057200869376392400656335

theorem tailTrace_3088337 : CollatzResearch.WordTrace tailWord_3088337 prefixEnd_3088337 1057200869376392400656335 := by
  unfold tailWord_3088337
  simp only [CollatzResearch.WordTrace]
  refine ⟨112640904212489969812591265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75093936141659979875060843 112640904212489969812591265)
  ·
    refine ⟨84480678159367477359443449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112640904212489969812591265 84480678159367477359443449)
    ·
      refine ⟨63360508619525608019582587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84480678159367477359443449 63360508619525608019582587)
      ·
        refine ⟨95040762929288412029373881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63360508619525608019582587 95040762929288412029373881)
        ·
          refine ⟨71280572196966309022030411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95040762929288412029373881 71280572196966309022030411)
          ·
            refine ⟨106920858295449463533045617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71280572196966309022030411 106920858295449463533045617)
            ·
              refine ⟨80190643721587097649784213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106920858295449463533045617 80190643721587097649784213)
              ·
                refine ⟨3758936424449395202333635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80190643721587097649784213 3758936424449395202333635)
                ·
                  refine ⟨5638404636674092803500453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758936424449395202333635 5638404636674092803500453)
                  ·
                    refine ⟨1057200869376392400656335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638404636674092803500453 1057200869376392400656335)
                    ·
                      rfl

theorem cell22_3088337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_3088337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088337 prefixEnd_3088337 := by exact prefixLift 3088337
  have htrace : WordTrace (prefixWord ++ tailWord_3088337) baseStart_3088337 baseEnd_3088337 := by
    simpa [prefixWord, tailWord_3088337, baseEnd_3088337] using wordTrace_append hprefix tailTrace_3088337
  have hstable : (prefixWord ++ tailWord_3088337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088337).length < 2 ^ (prefixWord ++ tailWord_3088337).sum := by decide
  have hdescent : baseEnd_3088337 < baseStart_3088337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088519 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3088519 : Nat := 118140960795 + 3088519 * 2 ^ 59
def prefixEnd_3088519 : Nat := 4983230072969 + 3 ^ 40 * 3088519 * 2
def baseEnd_3088519 : Nat := 1057263171695804592605777

theorem tailTrace_3088519 : CollatzResearch.WordTrace tailWord_3088519 prefixEnd_3088519 1057263171695804592605777 := by
  unfold tailWord_3088519
  simp only [CollatzResearch.WordTrace]
  refine ⟨112647542297830614895716611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75098361531887076597144407 112647542297830614895716611)
  ·
    refine ⟨168971313446745922343574917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112647542297830614895716611 168971313446745922343574917)
    ·
      refine ⟨31682121271264860439420297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168971313446745922343574917 31682121271264860439420297)
      ·
        refine ⟨23761590953448645329565223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31682121271264860439420297 23761590953448645329565223)
        ·
          refine ⟨35642386430172967994347835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23761590953448645329565223 35642386430172967994347835)
          ·
            refine ⟨53463579645259451991521753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35642386430172967994347835 53463579645259451991521753)
            ·
              refine ⟨40097684733944588993641315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53463579645259451991521753 40097684733944588993641315)
              ·
                refine ⟨60146527100916883490461973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40097684733944588993641315 60146527100916883490461973)
                ·
                  refine ⟨2819368457855478913615405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60146527100916883490461973 2819368457855478913615405)
                  ·
                    refine ⟨1057263171695804592605777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819368457855478913615405 1057263171695804592605777)
                    ·
                      rfl

theorem cell22_3088519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3088519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088519 prefixEnd_3088519 := by exact prefixLift 3088519
  have htrace : WordTrace (prefixWord ++ tailWord_3088519) baseStart_3088519 baseEnd_3088519 := by
    simpa [prefixWord, tailWord_3088519, baseEnd_3088519] using wordTrace_append hprefix tailTrace_3088519
  have hstable : (prefixWord ++ tailWord_3088519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088519).length < 2 ^ (prefixWord ++ tailWord_3088519).sum := by decide
  have hdescent : baseEnd_3088519 < baseStart_3088519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088538 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_3088538 : Nat := 118140960795 + 3088538 * 2 ^ 59
def prefixEnd_3088538 : Nat := 4983230072969 + 3 ^ 40 * 3088538 * 2
def baseEnd_3088538 : Nat := 352423225261364958793573

theorem tailTrace_3088538 : CollatzResearch.WordTrace tailWord_3088538 prefixEnd_3088538 352423225261364958793573 := by
  unfold tailWord_3088538
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162058821190445285164567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75098823523174520760438845 28162058821190445285164567)
  ·
    refine ⟨42243088231785667927746851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28162058821190445285164567 42243088231785667927746851)
    ·
      refine ⟨63364632347678501891620277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42243088231785667927746851 63364632347678501891620277)
      ·
        refine ⟨5940434282594859552339401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63364632347678501891620277 5940434282594859552339401)
        ·
          refine ⟨4455325711946144664254551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5940434282594859552339401 4455325711946144664254551)
          ·
            refine ⟨6682988567919216996381827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4455325711946144664254551 6682988567919216996381827)
            ·
              refine ⟨10024482851878825494572741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6682988567919216996381827 10024482851878825494572741)
              ·
                refine ⟨1879590534727279780232389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10024482851878825494572741 1879590534727279780232389)
                ·
                  refine ⟨352423225261364958793573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879590534727279780232389 352423225261364958793573)
                  ·
                    rfl

theorem cell22_3088538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_3088538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088538 prefixEnd_3088538 := by exact prefixLift 3088538
  have htrace : WordTrace (prefixWord ++ tailWord_3088538) baseStart_3088538 baseEnd_3088538 := by
    simpa [prefixWord, tailWord_3088538, baseEnd_3088538] using wordTrace_append hprefix tailTrace_3088538
  have hstable : (prefixWord ++ tailWord_3088538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088538).length < 2 ^ (prefixWord ++ tailWord_3088538).sum := by decide
  have hdescent : baseEnd_3088538 < baseStart_3088538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088547 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 4, 7]
def baseStart_3088547 : Nat := 118140960795 + 3088547 * 2 ^ 59
def prefixEnd_3088547 : Nat := 4983230072969 + 3 ^ 40 * 3088547 * 2
def baseEnd_3088547 : Nat := 1057272756668021852905691

theorem tailTrace_3088547 : CollatzResearch.WordTrace tailWord_3088547 prefixEnd_3088547 1057272756668021852905691 := by
  unfold tailWord_3088547
  simp only [CollatzResearch.WordTrace]
  refine ⟨112648563541729175677735895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75099042361152783785157263 112648563541729175677735895)
  ·
    refine ⟨168972845312593763516603843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112648563541729175677735895 168972845312593763516603843)
    ·
      refine ⟨253459267968890645274905765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168972845312593763516603843 253459267968890645274905765)
      ·
        refine ⟨47523612744166995989044831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253459267968890645274905765 47523612744166995989044831)
        ·
          refine ⟨71285419116250493983567247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47523612744166995989044831 71285419116250493983567247)
          ·
            refine ⟨106928128674375740975350871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71285419116250493983567247 106928128674375740975350871)
            ·
              refine ⟨160392193011563611463026307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106928128674375740975350871 160392193011563611463026307)
              ·
                refine ⟨240588289517345417194539461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160392193011563611463026307 240588289517345417194539461)
                ·
                  refine ⟨45110304284502265723976149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 240588289517345417194539461 45110304284502265723976149)
                  ·
                    refine ⟨1057272756668021852905691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45110304284502265723976149 1057272756668021852905691)
                    ·
                      rfl

theorem cell22_3088547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 7].length) (baseStart_3088547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088547 prefixEnd_3088547 := by exact prefixLift 3088547
  have htrace : WordTrace (prefixWord ++ tailWord_3088547) baseStart_3088547 baseEnd_3088547 := by
    simpa [prefixWord, tailWord_3088547, baseEnd_3088547] using wordTrace_append hprefix tailTrace_3088547
  have hstable : (prefixWord ++ tailWord_3088547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088547).length < 2 ^ (prefixWord ++ tailWord_3088547).sum := by decide
  have hdescent : baseEnd_3088547 < baseStart_3088547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088609 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3088609 : Nat := 118140960795 + 3088609 * 2 ^ 59
def prefixEnd_3088609 : Nat := 4983230072969 + 3 ^ 40 * 3088609 * 2
def baseEnd_3088609 : Nat := 1057293980535074357855501

theorem tailTrace_3088609 : CollatzResearch.WordTrace tailWord_3088609 prefixEnd_3088609 1057293980535074357855501 := by
  unfold tailWord_3088609
  simp only [CollatzResearch.WordTrace]
  refine ⟨112650824867504560266492881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75100549911669706844328587 112650824867504560266492881)
  ·
    refine ⟨84488118650628420199869661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112650824867504560266492881 84488118650628420199869661)
    ·
      refine ⟨31683044493985657574951123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84488118650628420199869661 31683044493985657574951123)
      ·
        refine ⟨47524566740978486362426685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31683044493985657574951123 47524566740978486362426685)
        ·
          refine ⟨17821712527866932385910007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47524566740978486362426685 17821712527866932385910007)
          ·
            refine ⟨26732568791800398578865011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17821712527866932385910007 26732568791800398578865011)
            ·
              refine ⟨40098853187700597868297517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26732568791800398578865011 40098853187700597868297517)
              ·
                refine ⟨15037069945387724200611569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40098853187700597868297517 15037069945387724200611569)
                ·
                  refine ⟨11277802459040793150458677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15037069945387724200611569 11277802459040793150458677)
                  ·
                    refine ⟨1057293980535074357855501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11277802459040793150458677 1057293980535074357855501)
                    ·
                      rfl

theorem cell22_3088609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3088609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088609 prefixEnd_3088609 := by exact prefixLift 3088609
  have htrace : WordTrace (prefixWord ++ tailWord_3088609) baseStart_3088609 baseEnd_3088609 := by
    simpa [prefixWord, tailWord_3088609, baseEnd_3088609] using wordTrace_append hprefix tailTrace_3088609
  have hstable : (prefixWord ++ tailWord_3088609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088609).length < 2 ^ (prefixWord ++ tailWord_3088609).sum := by decide
  have hdescent : baseEnd_3088609 < baseStart_3088609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088624 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_3088624 : Nat := 118140960795 + 3088624 * 2 ^ 59
def prefixEnd_3088624 : Nat := 4983230072969 + 3 ^ 40 * 3088624 * 2
def baseEnd_3088624 : Nat := 1057299115341619318730455

theorem tailTrace_3088624 : CollatzResearch.WordTrace tailWord_3088624 prefixEnd_3088624 1057299115341619318730455 := by
  unfold tailWord_3088624
  simp only [CollatzResearch.WordTrace]
  refine ⟨56325685981225108914144463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75100914641633478552192617 56325685981225108914144463)
  ·
    refine ⟨84488528971837663371216695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56325685981225108914144463 84488528971837663371216695)
    ·
      refine ⟨126732793457756495056825043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84488528971837663371216695 126732793457756495056825043)
      ·
        refine ⟨190099190186634742585237565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126732793457756495056825043 190099190186634742585237565)
        ·
          refine ⟨71287196319988028469464087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190099190186634742585237565 71287196319988028469464087)
          ·
            refine ⟨106930794479982042704196131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71287196319988028469464087 106930794479982042704196131)
            ·
              refine ⟨160396191719973064056294197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106930794479982042704196131 160396191719973064056294197)
              ·
                refine ⟨15037142973747474755277581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 160396191719973064056294197 15037142973747474755277581)
                ·
                  refine ⟨5638928615155303033229093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15037142973747474755277581 5638928615155303033229093)
                  ·
                    refine ⟨1057299115341619318730455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638928615155303033229093 1057299115341619318730455)
                    ·
                      rfl

theorem cell22_3088624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_3088624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088624 prefixEnd_3088624 := by exact prefixLift 3088624
  have htrace : WordTrace (prefixWord ++ tailWord_3088624) baseStart_3088624 baseEnd_3088624 := by
    simpa [prefixWord, tailWord_3088624, baseEnd_3088624] using wordTrace_append hprefix tailTrace_3088624
  have hstable : (prefixWord ++ tailWord_3088624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088624).length < 2 ^ (prefixWord ++ tailWord_3088624).sum := by decide
  have hdescent : baseEnd_3088624 < baseStart_3088624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088641 : List Nat := [1, 2, 4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3088641 : Nat := 118140960795 + 3088641 * 2 ^ 59
def prefixEnd_3088641 : Nat := 4983230072969 + 3 ^ 40 * 3088641 * 2
def baseEnd_3088641 : Nat := 1057304934789036941055403

theorem tailTrace_3088641 : CollatzResearch.WordTrace tailWord_3088641 prefixEnd_3088641 1057304934789036941055403 := by
  unfold tailWord_3088641
  simp only [CollatzResearch.WordTrace]
  refine ⟨112651992003388629731657777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75101328002259086487771851 112651992003388629731657777)
  ·
    refine ⟨84488994002541472298743333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112651992003388629731657777 84488994002541472298743333)
    ·
      refine ⟨15841686375476526056014375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84488994002541472298743333 15841686375476526056014375)
      ·
        refine ⟨23762529563214789084021563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15841686375476526056014375 23762529563214789084021563)
        ·
          refine ⟨35643794344822183626032345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23762529563214789084021563 35643794344822183626032345)
          ·
            refine ⟨26732845758616637719524259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35643794344822183626032345 26732845758616637719524259)
            ·
              refine ⟨40099268637924956579286389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26732845758616637719524259 40099268637924956579286389)
              ·
                refine ⟨3759306434805464679308099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40099268637924956579286389 3759306434805464679308099)
                ·
                  refine ⟨5638959652208197018962149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759306434805464679308099 5638959652208197018962149)
                  ·
                    refine ⟨1057304934789036941055403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5638959652208197018962149 1057304934789036941055403)
                    ·
                      rfl

theorem cell22_3088641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3088641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088641 prefixEnd_3088641 := by exact prefixLift 3088641
  have htrace : WordTrace (prefixWord ++ tailWord_3088641) baseStart_3088641 baseEnd_3088641 := by
    simpa [prefixWord, tailWord_3088641, baseEnd_3088641] using wordTrace_append hprefix tailTrace_3088641
  have hstable : (prefixWord ++ tailWord_3088641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088641).length < 2 ^ (prefixWord ++ tailWord_3088641).sum := by decide
  have hdescent : baseEnd_3088641 < baseStart_3088641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088684 : List Nat := [2, 2, 1, 1, 1, 3, 4, 8]
def baseStart_3088684 : Nat := 118140960795 + 3088684 * 2 ^ 59
def prefixEnd_3088684 : Nat := 4983230072969 + 3 ^ 40 * 3088684 * 2
def baseEnd_3088684 : Nat := 117479961618644351358919

theorem tailTrace_3088684 : CollatzResearch.WordTrace tailWord_3088684 prefixEnd_3088684 117479961618644351358919 := by
  unfold tailWord_3088684
  simp only [CollatzResearch.WordTrace]
  refine ⟨56326780171116424037736553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75102373561488565383648737 56326780171116424037736553)
  ·
    refine ⟨42245085128337318028302415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56326780171116424037736553 42245085128337318028302415)
    ·
      refine ⟨63367627692505977042453623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42245085128337318028302415 63367627692505977042453623)
      ·
        refine ⟨95051441538758965563680435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63367627692505977042453623 95051441538758965563680435)
        ·
          refine ⟨142577162308138448345520653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95051441538758965563680435 142577162308138448345520653)
          ·
            refine ⟨53466435865551918129570245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142577162308138448345520653 53466435865551918129570245)
            ·
              refine ⟨10024956724790984649294421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53466435865551918129570245 10024956724790984649294421)
              ·
                refine ⟨117479961618644351358919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10024956724790984649294421 117479961618644351358919)
                ·
                  rfl

theorem cell22_3088684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 8].length) (baseStart_3088684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088684 prefixEnd_3088684 := by exact prefixLift 3088684
  have htrace : WordTrace (prefixWord ++ tailWord_3088684) baseStart_3088684 baseEnd_3088684 := by
    simpa [prefixWord, tailWord_3088684, baseEnd_3088684] using wordTrace_append hprefix tailTrace_3088684
  have hstable : (prefixWord ++ tailWord_3088684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088684).length < 2 ^ (prefixWord ++ tailWord_3088684).sum := by decide
  have hdescent : baseEnd_3088684 < baseStart_3088684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088729 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 9]
def baseStart_3088729 : Nat := 118140960795 + 3088729 * 2 ^ 59
def prefixEnd_3088729 : Nat := 4983230072969 + 3 ^ 40 * 3088729 * 2
def baseEnd_3088729 : Nat := 352445019662478014951711

theorem tailTrace_3088729 : CollatzResearch.WordTrace tailWord_3088729 prefixEnd_3088729 352445019662478014951711 := by
  unfold tailWord_3088729
  simp only [CollatzResearch.WordTrace]
  refine ⟨112655201627069820760861241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75103467751379880507240827 112655201627069820760861241)
  ·
    refine ⟨84491401220302365570645931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112655201627069820760861241 84491401220302365570645931)
    ·
      refine ⟨126737101830453548355968897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84491401220302365570645931 126737101830453548355968897)
      ·
        refine ⟨95052826372840161266976673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126737101830453548355968897 95052826372840161266976673)
        ·
          refine ⟨71289619779630120950232505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95052826372840161266976673 71289619779630120950232505)
          ·
            refine ⟨53467214834722590712674379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71289619779630120950232505 53467214834722590712674379)
            ·
              refine ⟨80200822252083886069011569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53467214834722590712674379 80200822252083886069011569)
              ·
                refine ⟨60150616689062914551758677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80200822252083886069011569 60150616689062914551758677)
                ·
                  refine ⟨352445019662478014951711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60150616689062914551758677 352445019662478014951711)
                  ·
                    rfl

theorem cell22_3088729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_3088729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088729 prefixEnd_3088729 := by exact prefixLift 3088729
  have htrace : WordTrace (prefixWord ++ tailWord_3088729) baseStart_3088729 baseEnd_3088729 := by
    simpa [prefixWord, tailWord_3088729, baseEnd_3088729] using wordTrace_append hprefix tailTrace_3088729
  have hstable : (prefixWord ++ tailWord_3088729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088729).length < 2 ^ (prefixWord ++ tailWord_3088729).sum := by decide
  have hdescent : baseEnd_3088729 < baseStart_3088729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088763 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 5]
def baseStart_3088763 : Nat := 118140960795 + 3088763 * 2 ^ 59
def prefixEnd_3088763 : Nat := 4983230072969 + 3 ^ 40 * 3088763 * 2
def baseEnd_3088763 : Nat := 352448899294089763168343

theorem tailTrace_3088763 : CollatzResearch.WordTrace tailWord_3088763 prefixEnd_3088763 352448899294089763168343 := by
  unfold tailWord_3088763
  simp only [CollatzResearch.WordTrace]
  refine ⟨112656441708946644567598943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75104294472631096378399295 112656441708946644567598943)
  ·
    refine ⟨168984662563419966851398415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112656441708946644567598943 168984662563419966851398415)
    ·
      refine ⟨253476993845129950277097623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168984662563419966851398415 253476993845129950277097623)
      ·
        refine ⟨380215490767694925415646435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253476993845129950277097623 380215490767694925415646435)
        ·
          refine ⟨570323236151542388123469653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380215490767694925415646435 570323236151542388123469653)
          ·
            refine ⟨3341737711825443680410955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 570323236151542388123469653 3341737711825443680410955)
            ·
              refine ⟨5012606567738165520616433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341737711825443680410955 5012606567738165520616433)
              ·
                refine ⟨3759454925803624140462325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012606567738165520616433 3759454925803624140462325)
                ·
                  refine ⟨352448899294089763168343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3759454925803624140462325 352448899294089763168343)
                  ·
                    rfl

theorem cell22_3088763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 5].length) (baseStart_3088763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088763 prefixEnd_3088763 := by exact prefixLift 3088763
  have htrace : WordTrace (prefixWord ++ tailWord_3088763) baseStart_3088763 baseEnd_3088763 := by
    simpa [prefixWord, tailWord_3088763, baseEnd_3088763] using wordTrace_append hprefix tailTrace_3088763
  have hstable : (prefixWord ++ tailWord_3088763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088763).length < 2 ^ (prefixWord ++ tailWord_3088763).sum := by decide
  have hdescent : baseEnd_3088763 < baseStart_3088763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088791 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 6]
def baseStart_3088791 : Nat := 118140960795 + 3088791 * 2 ^ 59
def prefixEnd_3088791 : Nat := 4983230072969 + 3 ^ 40 * 3088791 * 2
def baseEnd_3088791 : Nat := 352452094284828849934981

theorem tailTrace_3088791 : CollatzResearch.WordTrace tailWord_3088791 prefixEnd_3088791 352452094284828849934981 := by
  unfold tailWord_3088791
  simp only [CollatzResearch.WordTrace]
  refine ⟨112657462952845205349618227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75104975301896803566412151 112657462952845205349618227)
  ·
    refine ⟨168986194429267808024427341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112657462952845205349618227 168986194429267808024427341)
    ·
      refine ⟨63369822910975428009160253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168986194429267808024427341 63369822910975428009160253)
      ·
        refine ⟨23763683591615785503435095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63369822910975428009160253 23763683591615785503435095)
        ·
          refine ⟨35645525387423678255152643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23763683591615785503435095 35645525387423678255152643)
          ·
            refine ⟨53468288081135517382728965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35645525387423678255152643 53468288081135517382728965)
            ·
              refine ⟨10025304015212909509261681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53468288081135517382728965 10025304015212909509261681)
              ·
                refine ⟨7518978011409682131946261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10025304015212909509261681 7518978011409682131946261)
                ·
                  refine ⟨352452094284828849934981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7518978011409682131946261 352452094284828849934981)
                  ·
                    rfl

theorem cell22_3088791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 6].length) (baseStart_3088791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088791 prefixEnd_3088791 := by exact prefixLift 3088791
  have htrace : WordTrace (prefixWord ++ tailWord_3088791) baseStart_3088791 baseEnd_3088791 := by
    simpa [prefixWord, tailWord_3088791, baseEnd_3088791] using wordTrace_append hprefix tailTrace_3088791
  have hstable : (prefixWord ++ tailWord_3088791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088791).length < 2 ^ (prefixWord ++ tailWord_3088791).sum := by decide
  have hdescent : baseEnd_3088791 < baseStart_3088791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088793 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_3088793 : Nat := 118140960795 + 3088793 * 2 ^ 59
def prefixEnd_3088793 : Nat := 4983230072969 + 3 ^ 40 * 3088793 * 2
def baseEnd_3088793 : Nat := 1057356967495359211254937

theorem tailTrace_3088793 : CollatzResearch.WordTrace tailWord_3088793 prefixEnd_3088793 1057356967495359211254937 := by
  unfold tailWord_3088793
  simp only [CollatzResearch.WordTrace]
  refine ⟨112657535898837959691191033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75105023932558639794127355 112657535898837959691191033)
  ·
    refine ⟨84493151924128469768393275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112657535898837959691191033 84493151924128469768393275)
    ·
      refine ⟨126739727886192704652589913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84493151924128469768393275 126739727886192704652589913)
      ·
        refine ⟨95054795914644528489442435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126739727886192704652589913 95054795914644528489442435)
        ·
          refine ⟨142582193871966792734163653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95054795914644528489442435 142582193871966792734163653)
          ·
            refine ⟨26734161350993773637655685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142582193871966792734163653 26734161350993773637655685)
            ·
              refine ⟨5012655253311332557060441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26734161350993773637655685 5012655253311332557060441)
              ·
                refine ⟨3759491439983499417795331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5012655253311332557060441 3759491439983499417795331)
                ·
                  refine ⟨5639237159975249126692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759491439983499417795331 5639237159975249126692997)
                  ·
                    refine ⟨1057356967495359211254937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639237159975249126692997 1057356967495359211254937)
                    ·
                      rfl

theorem cell22_3088793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_3088793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088793 prefixEnd_3088793 := by exact prefixLift 3088793
  have htrace : WordTrace (prefixWord ++ tailWord_3088793) baseStart_3088793 baseEnd_3088793 := by
    simpa [prefixWord, tailWord_3088793, baseEnd_3088793] using wordTrace_append hprefix tailTrace_3088793
  have hstable : (prefixWord ++ tailWord_3088793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088793).length < 2 ^ (prefixWord ++ tailWord_3088793).sum := by decide
  have hdescent : baseEnd_3088793 < baseStart_3088793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088801 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 1, 3]
def baseStart_3088801 : Nat := 118140960795 + 3088801 * 2 ^ 59
def prefixEnd_3088801 : Nat := 4983230072969 + 3 ^ 40 * 3088801 * 2
def baseEnd_3088801 : Nat := 1057359706058849857054913

theorem tailTrace_3088801 : CollatzResearch.WordTrace tailWord_3088801 prefixEnd_3088801 1057359706058849857054913 := by
  unfold tailWord_3088801
  simp only [CollatzResearch.WordTrace]
  refine ⟨112657827682808977057482257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75105218455205984704988171 112657827682808977057482257)
  ·
    refine ⟨84493370762106732793111693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112657827682808977057482257 84493370762106732793111693)
    ·
      refine ⟨31685014035790024797416885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84493370762106732793111693 31685014035790024797416885)
      ·
        refine ⟨2970470065855314824757833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31685014035790024797416885 2970470065855314824757833)
        ·
          refine ⟨2227852549391486118568375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2970470065855314824757833 2227852549391486118568375)
          ·
            refine ⟨3341778824087229177852563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2227852549391486118568375 3341778824087229177852563)
            ·
              refine ⟨5012668236130843766778845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341778824087229177852563 5012668236130843766778845)
              ·
                refine ⟨1879750588549066412542067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5012668236130843766778845 1879750588549066412542067)
                ·
                  refine ⟨2819625882823599618813101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879750588549066412542067 2819625882823599618813101)
                  ·
                    refine ⟨1057359706058849857054913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819625882823599618813101 1057359706058849857054913)
                    ·
                      rfl

theorem cell22_3088801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_3088801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088801 prefixEnd_3088801 := by exact prefixLift 3088801
  have htrace : WordTrace (prefixWord ++ tailWord_3088801) baseStart_3088801 baseEnd_3088801 := by
    simpa [prefixWord, tailWord_3088801, baseEnd_3088801] using wordTrace_append hprefix tailTrace_3088801
  have hstable : (prefixWord ++ tailWord_3088801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088801).length < 2 ^ (prefixWord ++ tailWord_3088801).sum := by decide
  have hdescent : baseEnd_3088801 < baseStart_3088801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088823 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 4, 3]
def baseStart_3088823 : Nat := 118140960795 + 3088823 * 2 ^ 59
def prefixEnd_3088823 : Nat := 4983230072969 + 3 ^ 40 * 3088823 * 2
def baseEnd_3088823 : Nat := 1057367237108449133004845

theorem tailTrace_3088823 : CollatzResearch.WordTrace tailWord_3088823 prefixEnd_3088823 1057367237108449133004845 := by
  unfold tailWord_3088823
  simp only [CollatzResearch.WordTrace]
  refine ⟨112658630088729274814783123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75105753392486183209855415 112658630088729274814783123)
  ·
    refine ⟨168987945133093912222174685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112658630088729274814783123 168987945133093912222174685)
    ·
      refine ⟨63370479424910217083315507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168987945133093912222174685 63370479424910217083315507)
      ·
        refine ⟨95055719137365325624973261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63370479424910217083315507 95055719137365325624973261)
        ·
          refine ⟨35645894676511997109364973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95055719137365325624973261 35645894676511997109364973)
          ·
            refine ⟨13367210503691998916011865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35645894676511997109364973 13367210503691998916011865)
            ·
              refine ⟨10025407877768999187008899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13367210503691998916011865 10025407877768999187008899)
              ·
                refine ⟨15038111816653498780513349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10025407877768999187008899 15038111816653498780513349)
                ·
                  refine ⟨2819645965622531021346253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15038111816653498780513349 2819645965622531021346253)
                  ·
                    refine ⟨1057367237108449133004845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819645965622531021346253 1057367237108449133004845)
                    ·
                      rfl

theorem cell22_3088823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_3088823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088823 prefixEnd_3088823 := by exact prefixLift 3088823
  have htrace : WordTrace (prefixWord ++ tailWord_3088823) baseStart_3088823 baseEnd_3088823 := by
    simpa [prefixWord, tailWord_3088823, baseEnd_3088823] using wordTrace_append hprefix tailTrace_3088823
  have hstable : (prefixWord ++ tailWord_3088823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088823).length < 2 ^ (prefixWord ++ tailWord_3088823).sum := by decide
  have hdescent : baseEnd_3088823 < baseStart_3088823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088840 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_3088840 : Nat := 118140960795 + 3088840 * 2 ^ 59
def prefixEnd_3088840 : Nat := 4983230072969 + 3 ^ 40 * 3088840 * 2
def baseEnd_3088840 : Nat := 1057373056555866755329793

theorem tailTrace_3088840 : CollatzResearch.WordTrace tailWord_3088840 prefixEnd_3088840 1057373056555866755329793 := by
  unfold tailWord_3088840
  simp only [CollatzResearch.WordTrace]
  refine ⟨56329625064833843359075987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75106166753111791145434649 56329625064833843359075987)
  ·
    refine ⟨84494437597250765038613981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56329625064833843359075987 84494437597250765038613981)
    ·
      refine ⟨31685414098969036889480243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84494437597250765038613981 31685414098969036889480243)
      ·
        refine ⟨47528121148453555334220365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31685414098969036889480243 47528121148453555334220365)
        ·
          refine ⟨17823045430670083250332637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47528121148453555334220365 17823045430670083250332637)
          ·
            refine ⟨6683642036501281218874739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17823045430670083250332637 6683642036501281218874739)
            ·
              refine ⟨10025463054751921828312109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683642036501281218874739 10025463054751921828312109)
              ·
                refine ⟨3759548645531970685617041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10025463054751921828312109 3759548645531970685617041)
                ·
                  refine ⟨2819661484148978014212781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3759548645531970685617041 2819661484148978014212781)
                  ·
                    refine ⟨1057373056555866755329793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819661484148978014212781 1057373056555866755329793)
                    ·
                      rfl

theorem cell22_3088840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_3088840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088840 prefixEnd_3088840 := by exact prefixLift 3088840
  have htrace : WordTrace (prefixWord ++ tailWord_3088840) baseStart_3088840 baseEnd_3088840 := by
    simpa [prefixWord, tailWord_3088840, baseEnd_3088840] using wordTrace_append hprefix tailTrace_3088840
  have hstable : (prefixWord ++ tailWord_3088840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088840).length < 2 ^ (prefixWord ++ tailWord_3088840).sum := by decide
  have hdescent : baseEnd_3088840 < baseStart_3088840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088977 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 4]
def baseStart_3088977 : Nat := 118140960795 + 3088977 * 2 ^ 59
def prefixEnd_3088977 : Nat := 4983230072969 + 3 ^ 40 * 3088977 * 2
def baseEnd_3088977 : Nat := 352473318151881354884791

theorem tailTrace_3088977 : CollatzResearch.WordTrace tailWord_3088977 prefixEnd_3088977 352473318151881354884791 := by
  unfold tailWord_3088977
  simp only [CollatzResearch.WordTrace]
  refine ⟨112664246930171359115889185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75109497953447572743926123 112664246930171359115889185)
  ·
    refine ⟨84498185197628519336916889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112664246930171359115889185 84498185197628519336916889)
    ·
      refine ⟨63373638898221389502687667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84498185197628519336916889 63373638898221389502687667)
      ·
        refine ⟨95060458347332084254031501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63373638898221389502687667 95060458347332084254031501)
        ·
          refine ⟨35647671880249531595261813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95060458347332084254031501 35647671880249531595261813)
          ·
            refine ⟨3341969238773393587055795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35647671880249531595261813 3341969238773393587055795)
            ·
              refine ⟨5012953858160090380583693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341969238773393587055795 5012953858160090380583693)
              ·
                refine ⟨1879857696810033892718885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5012953858160090380583693 1879857696810033892718885)
                ·
                  refine ⟨352473318151881354884791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879857696810033892718885 352473318151881354884791)
                  ·
                    rfl

theorem cell22_3088977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 4].length) (baseStart_3088977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088977 prefixEnd_3088977 := by exact prefixLift 3088977
  have htrace : WordTrace (prefixWord ++ tailWord_3088977) baseStart_3088977 baseEnd_3088977 := by
    simpa [prefixWord, tailWord_3088977, baseEnd_3088977] using wordTrace_append hprefix tailTrace_3088977
  have hstable : (prefixWord ++ tailWord_3088977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088977).length < 2 ^ (prefixWord ++ tailWord_3088977).sum := by decide
  have hdescent : baseEnd_3088977 < baseStart_3088977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3088994 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_3088994 : Nat := 118140960795 + 3088994 * 2 ^ 59
def prefixEnd_3088994 : Nat := 4983230072969 + 3 ^ 40 * 3088994 * 2
def baseEnd_3088994 : Nat := 352475257967687228993107

theorem tailTrace_3088994 : CollatzResearch.WordTrace tailWord_3088994 prefixEnd_3088994 352475257967687228993107 := by
  unfold tailWord_3088994
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166216742777442754814509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75109911314073180679505357 28166216742777442754814509)
  ·
    refine ⟨10562331278541541033055441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28166216742777442754814509 10562331278541541033055441)
    ·
      refine ⟨7921748458906155774791581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10562331278541541033055441 7921748458906155774791581)
      ·
        refine ⟨2970655672089808415546843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7921748458906155774791581 2970655672089808415546843)
        ·
          refine ⟨4455983508134712623320265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970655672089808415546843 4455983508134712623320265)
          ·
            refine ⟨3341987631101034467490199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4455983508134712623320265 3341987631101034467490199)
            ·
              refine ⟨5012981446651551701235299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341987631101034467490199 5012981446651551701235299)
              ·
                refine ⟨7519472169977327551852949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5012981446651551701235299 7519472169977327551852949)
                ·
                  refine ⟨352475257967687228993107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7519472169977327551852949 352475257967687228993107)
                  ·
                    rfl

theorem cell22_3088994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_3088994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3088994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3088994 prefixEnd_3088994 := by exact prefixLift 3088994
  have htrace : WordTrace (prefixWord ++ tailWord_3088994) baseStart_3088994 baseEnd_3088994 := by
    simpa [prefixWord, tailWord_3088994, baseEnd_3088994] using wordTrace_append hprefix tailTrace_3088994
  have hstable : (prefixWord ++ tailWord_3088994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3088994).length < 2 ^ (prefixWord ++ tailWord_3088994).sum := by decide
  have hdescent : baseEnd_3088994 < baseStart_3088994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3088994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089005 : List Nat := [1, 5, 1, 1, 3, 2, 2, 7]
def baseStart_3089005 : Nat := 118140960795 + 3089005 * 2 ^ 59
def prefixEnd_3089005 : Nat := 4983230072969 + 3 ^ 40 * 3089005 * 2
def baseEnd_3089005 : Nat := 117492171047540147217143

theorem tailTrace_3089005 : CollatzResearch.WordTrace tailWord_3089005 prefixEnd_3089005 117492171047540147217143 := by
  unfold tailWord_3089005
  simp only [CollatzResearch.WordTrace]
  refine ⟨112665268174069919897908469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75110178782713279931938979 112665268174069919897908469)
  ·
    refine ⟨10562368891319054990428919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112665268174069919897908469 10562368891319054990428919)
    ·
      refine ⟨15843553336978582485643379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10562368891319054990428919 15843553336978582485643379)
      ·
        refine ⟨23765330005467873728465069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15843553336978582485643379 23765330005467873728465069)
        ·
          refine ⟨8911998752050452648174401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23765330005467873728465069 8911998752050452648174401)
          ·
            refine ⟨6683999064037839486130801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8911998752050452648174401 6683999064037839486130801)
            ·
              refine ⟨5012999298028379614598101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6683999064037839486130801 5012999298028379614598101)
              ·
                refine ⟨117492171047540147217143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5012999298028379614598101 117492171047540147217143)
                ·
                  rfl

theorem cell22_3089005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 7].length) (baseStart_3089005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089005 prefixEnd_3089005 := by exact prefixLift 3089005
  have htrace : WordTrace (prefixWord ++ tailWord_3089005) baseStart_3089005 baseEnd_3089005 := by
    simpa [prefixWord, tailWord_3089005, baseEnd_3089005] using wordTrace_append hprefix tailTrace_3089005
  have hstable : (prefixWord ++ tailWord_3089005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089005).length < 2 ^ (prefixWord ++ tailWord_3089005).sum := by decide
  have hdescent : baseEnd_3089005 < baseStart_3089005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089020 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_3089020 : Nat := 118140960795 + 3089020 * 2 ^ 59
def prefixEnd_3089020 : Nat := 4983230072969 + 3 ^ 40 * 3089020 * 2
def baseEnd_3089020 : Nat := 1057434674234406285829241

theorem tailTrace_3089020 : CollatzResearch.WordTrace tailWord_3089020 prefixEnd_3089020 1057434674234406285829241 := by
  unfold tailWord_3089020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56332907634507788729852257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75110543512677051639803009 56332907634507788729852257)
  ·
    refine ⟨42249680725880841547389193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56332907634507788729852257 42249680725880841547389193)
    ·
      refine ⟨31687260544410631160541895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42249680725880841547389193 31687260544410631160541895)
      ·
        refine ⟨47530890816615946740812843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31687260544410631160541895 47530890816615946740812843)
        ·
          refine ⟨71296336224923920111219265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47530890816615946740812843 71296336224923920111219265)
          ·
            refine ⟨53472252168692940083414449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71296336224923920111219265 53472252168692940083414449)
            ·
              refine ⟨40104189126519705062560837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53472252168692940083414449 40104189126519705062560837)
              ·
                refine ⟨7519535461222444699230157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40104189126519705062560837 7519535461222444699230157)
                ·
                  refine ⟨2819825797958416762211309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7519535461222444699230157 2819825797958416762211309)
                  ·
                    refine ⟨1057434674234406285829241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2819825797958416762211309 1057434674234406285829241)
                    ·
                      rfl

theorem cell22_3089020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_3089020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089020 prefixEnd_3089020 := by exact prefixLift 3089020
  have htrace : WordTrace (prefixWord ++ tailWord_3089020) baseStart_3089020 baseEnd_3089020 := by
    simpa [prefixWord, tailWord_3089020, baseEnd_3089020] using wordTrace_append hprefix tailTrace_3089020
  have hstable : (prefixWord ++ tailWord_3089020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089020).length < 2 ^ (prefixWord ++ tailWord_3089020).sum := by decide
  have hdescent : baseEnd_3089020 < baseStart_3089020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089026 : List Nat := [3, 4, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3089026 : Nat := 118140960795 + 3089026 * 2 ^ 59
def prefixEnd_3089026 : Nat := 4983230072969 + 3 ^ 40 * 3089026 * 2
def baseEnd_3089026 : Nat := 1057436728157024270179223

theorem tailTrace_3089026 : CollatzResearch.WordTrace tailWord_3089026 prefixEnd_3089026 1057436728157024270179223 := by
  unfold tailWord_3089026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166508526748460121105733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75110689404662560322948621 28166508526748460121105733)
  ·
    refine ⟨5281220348765336272707325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28166508526748460121105733 5281220348765336272707325)
    ·
      refine ⟨1980457630787001102265247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5281220348765336272707325 1980457630787001102265247)
      ·
        refine ⟨2970686446180501653397871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980457630787001102265247 2970686446180501653397871)
        ·
          refine ⟨4456029669270752480096807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970686446180501653397871 4456029669270752480096807)
          ·
            refine ⟨6684044503906128720145211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4456029669270752480096807 6684044503906128720145211)
            ·
              refine ⟨10026066755859193080217817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684044503906128720145211 10026066755859193080217817)
              ·
                refine ⟨7519550066894394810163363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10026066755859193080217817 7519550066894394810163363)
                ·
                  refine ⟨11279325100341592215245045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7519550066894394810163363 11279325100341592215245045)
                  ·
                    refine ⟨1057436728157024270179223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11279325100341592215245045 1057436728157024270179223)
                    ·
                      rfl

theorem cell22_3089026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3089026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089026 prefixEnd_3089026 := by exact prefixLift 3089026
  have htrace : WordTrace (prefixWord ++ tailWord_3089026) baseStart_3089026 baseEnd_3089026 := by
    simpa [prefixWord, tailWord_3089026, baseEnd_3089026] using wordTrace_append hprefix tailTrace_3089026
  have hstable : (prefixWord ++ tailWord_3089026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089026).length < 2 ^ (prefixWord ++ tailWord_3089026).sum := by decide
  have hdescent : baseEnd_3089026 < baseStart_3089026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089101 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3089101 : Nat := 118140960795 + 3089101 * 2 ^ 59
def prefixEnd_3089101 : Nat := 4983230072969 + 3 ^ 40 * 3089101 * 2
def baseEnd_3089101 : Nat := 352487467396583024851331

theorem tailTrace_3089101 : CollatzResearch.WordTrace tailWord_3089101 prefixEnd_3089101 352487467396583024851331 := by
  unfold tailWord_3089101
  simp only [CollatzResearch.WordTrace]
  refine ⟨112668769581722128293403157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75112513054481418862268771 112668769581722128293403157)
  ·
    refine ⟨5281348574143224763753273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 112668769581722128293403157 5281348574143224763753273)
    ·
      refine ⟨3961011430607418572814955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5281348574143224763753273 3961011430607418572814955)
      ·
        refine ⟨5941517145911127859222433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3961011430607418572814955 5941517145911127859222433)
        ·
          refine ⟨4456137859433345894416825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5941517145911127859222433 4456137859433345894416825)
          ·
            refine ⟨3342103394575009420812619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4456137859433345894416825 3342103394575009420812619)
            ·
              refine ⟨5013155091862514131218929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342103394575009420812619 5013155091862514131218929)
              ·
                refine ⟨3759866318896885598414197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013155091862514131218929 3759866318896885598414197)
                ·
                  refine ⟨352487467396583024851331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3759866318896885598414197 352487467396583024851331)
                  ·
                    rfl

theorem cell22_3089101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3089101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089101 prefixEnd_3089101 := by exact prefixLift 3089101
  have htrace : WordTrace (prefixWord ++ tailWord_3089101) baseStart_3089101 baseEnd_3089101 := by
    simpa [prefixWord, tailWord_3089101, baseEnd_3089101] using wordTrace_append hprefix tailTrace_3089101
  have hstable : (prefixWord ++ tailWord_3089101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089101).length < 2 ^ (prefixWord ++ tailWord_3089101).sum := by decide
  have hdescent : baseEnd_3089101 < baseStart_3089101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089112 : List Nat := [2, 1, 2, 2, 3, 2, 2, 4, 4]
def baseStart_3089112 : Nat := 118140960795 + 3089112 * 2 ^ 59
def prefixEnd_3089112 : Nat := 4983230072969 + 3 ^ 40 * 3089112 * 2
def baseEnd_3089112 : Nat := 352488722571516237509653

theorem tailTrace_3089112 : CollatzResearch.WordTrace tailWord_3089112 prefixEnd_3089112 352488722571516237509653 := by
  unfold tailWord_3089112
  simp only [CollatzResearch.WordTrace]
  refine ⟨56334585392341138586026795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75112780523121518114702393 56334585392341138586026795)
  ·
    refine ⟨84501878088511707879040193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56334585392341138586026795 84501878088511707879040193)
    ·
      refine ⟨63376408566383780909280145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84501878088511707879040193 63376408566383780909280145)
      ·
        refine ⟨47532306424787835681960109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63376408566383780909280145 47532306424787835681960109)
        ·
          refine ⟨17824614909295438380735041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47532306424787835681960109 17824614909295438380735041)
          ·
            refine ⟨13368461181971578785551281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17824614909295438380735041 13368461181971578785551281)
            ·
              refine ⟨10026345886478684089163461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13368461181971578785551281 10026345886478684089163461)
              ·
                refine ⟨1879939853714753266718149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10026345886478684089163461 1879939853714753266718149)
                ·
                  refine ⟨352488722571516237509653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1879939853714753266718149 352488722571516237509653)
                  ·
                    rfl

theorem cell22_3089112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_3089112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089112 prefixEnd_3089112 := by exact prefixLift 3089112
  have htrace : WordTrace (prefixWord ++ tailWord_3089112) baseStart_3089112 baseEnd_3089112 := by
    simpa [prefixWord, tailWord_3089112, baseEnd_3089112] using wordTrace_append hprefix tailTrace_3089112
  have hstable : (prefixWord ++ tailWord_3089112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089112).length < 2 ^ (prefixWord ++ tailWord_3089112).sum := by decide
  have hdescent : baseEnd_3089112 < baseStart_3089112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089125 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 1, 6]
def baseStart_3089125 : Nat := 118140960795 + 3089125 * 2 ^ 59
def prefixEnd_3089125 : Nat := 4983230072969 + 3 ^ 40 * 3089125 * 2
def baseEnd_3089125 : Nat := 1057470617880221011953919

theorem tailTrace_3089125 : CollatzResearch.WordTrace tailWord_3089125 prefixEnd_3089125 1057470617880221011953919 := by
  unfold tailWord_3089125
  simp only [CollatzResearch.WordTrace]
  refine ⟨112669644933635180392276829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75113096622423453594851219 112669644933635180392276829)
  ·
    refine ⟨42251116850113192647103811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112669644933635180392276829 42251116850113192647103811)
    ·
      refine ⟨63376675275169788970655717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42251116850113192647103811 63376675275169788970655717)
      ·
        refine ⟨11883126614094335431997947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63376675275169788970655717 11883126614094335431997947)
        ·
          refine ⟨17824689921141503147996921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11883126614094335431997947 17824689921141503147996921)
          ·
            refine ⟨13368517440856127360997691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17824689921141503147996921 13368517440856127360997691)
            ·
              refine ⟨20052776161284191041496537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368517440856127360997691 20052776161284191041496537)
              ·
                refine ⟨15039582120963143281122403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20052776161284191041496537 15039582120963143281122403)
                ·
                  refine ⟨22559373181444714921683605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15039582120963143281122403 22559373181444714921683605)
                  ·
                    refine ⟨1057470617880221011953919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22559373181444714921683605 1057470617880221011953919)
                    ·
                      rfl

theorem cell22_3089125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 6].length) (baseStart_3089125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089125 prefixEnd_3089125 := by exact prefixLift 3089125
  have htrace : WordTrace (prefixWord ++ tailWord_3089125) baseStart_3089125 baseEnd_3089125 := by
    simpa [prefixWord, tailWord_3089125, baseEnd_3089125] using wordTrace_append hprefix tailTrace_3089125
  have hstable : (prefixWord ++ tailWord_3089125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089125).length < 2 ^ (prefixWord ++ tailWord_3089125).sum := by decide
  have hdescent : baseEnd_3089125 < baseStart_3089125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089142 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3089142 : Nat := 118140960795 + 3089142 * 2 ^ 59
def prefixEnd_3089142 : Nat := 4983230072969 + 3 ^ 40 * 3089142 * 2
def baseEnd_3089142 : Nat := 1057476437327638634278867

theorem tailTrace_3089142 : CollatzResearch.WordTrace tailWord_3089142 prefixEnd_3089142 1057476437327638634278867 := by
  unfold tailWord_3089142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041891560910849518477855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75113509983049061530430453 7041891560910849518477855)
  ·
    refine ⟨10562837341366274277716783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7041891560910849518477855 10562837341366274277716783)
    ·
      refine ⟨15844256012049411416575175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10562837341366274277716783 15844256012049411416575175)
      ·
        refine ⟨23766384018074117124862763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15844256012049411416575175 23766384018074117124862763)
        ·
          refine ⟨35649576027111175687294145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23766384018074117124862763 35649576027111175687294145)
          ·
            refine ⟨26737182020333381765470609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35649576027111175687294145 26737182020333381765470609)
            ·
              refine ⟨20052886515250036324102957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26737182020333381765470609 20052886515250036324102957)
              ·
                refine ⟨7519832443218763621538609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20052886515250036324102957 7519832443218763621538609)
                ·
                  refine ⟨5639874332414072716153957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7519832443218763621538609 5639874332414072716153957)
                  ·
                    refine ⟨1057476437327638634278867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5639874332414072716153957 1057476437327638634278867)
                    ·
                      rfl

theorem cell22_3089142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3089142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089142 prefixEnd_3089142 := by exact prefixLift 3089142
  have htrace : WordTrace (prefixWord ++ tailWord_3089142) baseStart_3089142 baseEnd_3089142 := by
    simpa [prefixWord, tailWord_3089142, baseEnd_3089142] using wordTrace_append hprefix tailTrace_3089142
  have hstable : (prefixWord ++ tailWord_3089142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089142).length < 2 ^ (prefixWord ++ tailWord_3089142).sum := by decide
  have hdescent : baseEnd_3089142 < baseStart_3089142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089230 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_3089230 : Nat := 118140960795 + 3089230 * 2 ^ 59
def prefixEnd_3089230 : Nat := 4983230072969 + 3 ^ 40 * 3089230 * 2
def baseEnd_3089230 : Nat := 352502187175345246026199

theorem tailTrace_3089230 : CollatzResearch.WordTrace tailWord_3089230 prefixEnd_3089230 352502187175345246026199 := by
  unfold tailWord_3089230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14084184324781847915606143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75115649732169855549899429 14084184324781847915606143)
  ·
    refine ⟨21126276487172771873409215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14084184324781847915606143 21126276487172771873409215)
    ·
      refine ⟨31689414730759157810113823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21126276487172771873409215 31689414730759157810113823)
      ·
        refine ⟨47534122096138736715170735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31689414730759157810113823 47534122096138736715170735)
        ·
          refine ⟨71301183144208105072756103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47534122096138736715170735 71301183144208105072756103)
          ·
            refine ⟨106951774716312157609134155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71301183144208105072756103 106951774716312157609134155)
            ·
              refine ⟨160427662074468236413701233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106951774716312157609134155 160427662074468236413701233)
              ·
                refine ⟨120320746555851177310275925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 160427662074468236413701233 120320746555851177310275925)
                ·
                  refine ⟨352502187175345246026199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 120320746555851177310275925 352502187175345246026199)
                  ·
                    rfl

theorem cell22_3089230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_3089230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089230 prefixEnd_3089230 := by exact prefixLift 3089230
  have htrace : WordTrace (prefixWord ++ tailWord_3089230) baseStart_3089230 baseEnd_3089230 := by
    simpa [prefixWord, tailWord_3089230, baseEnd_3089230] using wordTrace_append hprefix tailTrace_3089230
  have hstable : (prefixWord ++ tailWord_3089230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089230).length < 2 ^ (prefixWord ++ tailWord_3089230).sum := by decide
  have hdescent : baseEnd_3089230 < baseStart_3089230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089277 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_3089277 : Nat := 118140960795 + 3089277 * 2 ^ 59
def prefixEnd_3089277 : Nat := 4983230072969 + 3 ^ 40 * 3089277 * 2
def baseEnd_3089277 : Nat := 1057522650586543282153453

theorem tailTrace_3089277 : CollatzResearch.WordTrace tailWord_3089277 prefixEnd_3089277 1057522650586543282153453 := by
  unfold tailWord_3089277
  simp only [CollatzResearch.WordTrace]
  refine ⟨112675188829084510351810085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75116792552723006901206723 112675188829084510351810085)
  ·
    refine ⟨21126597905453345690964391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112675188829084510351810085 21126597905453345690964391)
    ·
      refine ⟨31689896858180018536446587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21126597905453345690964391 31689896858180018536446587)
      ·
        refine ⟨47534845287270027804669881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31689896858180018536446587 47534845287270027804669881)
        ·
          refine ⟨35651133965452520853502411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47534845287270027804669881 35651133965452520853502411)
          ·
            refine ⟨53476700948178781280253617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35651133965452520853502411 53476700948178781280253617)
            ·
              refine ⟨40107525711134085960190213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53476700948178781280253617 40107525711134085960190213)
              ·
                refine ⟨7520161070837641117535665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40107525711134085960190213 7520161070837641117535665)
                ·
                  refine ⟨5640120803128230838151749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7520161070837641117535665 5640120803128230838151749)
                  ·
                    refine ⟨1057522650586543282153453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640120803128230838151749 1057522650586543282153453)
                    ·
                      rfl

theorem cell22_3089277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_3089277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089277 prefixEnd_3089277 := by exact prefixLift 3089277
  have htrace : WordTrace (prefixWord ++ tailWord_3089277) baseStart_3089277 baseEnd_3089277 := by
    simpa [prefixWord, tailWord_3089277, baseEnd_3089277] using wordTrace_append hprefix tailTrace_3089277
  have hstable : (prefixWord ++ tailWord_3089277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089277).length < 2 ^ (prefixWord ++ tailWord_3089277).sum := by decide
  have hdescent : baseEnd_3089277 < baseStart_3089277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089279 : List Nat := [1, 1, 2, 2, 1, 1, 7, 2, 2, 3]
def baseStart_3089279 : Nat := 118140960795 + 3089279 * 2 ^ 59
def prefixEnd_3089279 : Nat := 4983230072969 + 3 ^ 40 * 3089279 * 2
def baseEnd_3089279 : Nat := 1057523335227415943603447

theorem tailTrace_3089279 : CollatzResearch.WordTrace tailWord_3089279 prefixEnd_3089279 1057523335227415943603447 := by
  unfold tailWord_3089279
  simp only [CollatzResearch.WordTrace]
  refine ⟨112675261775077264693382891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75116841183384843128921927 112675261775077264693382891)
  ·
    refine ⟨169012892662615897040074337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112675261775077264693382891 169012892662615897040074337)
    ·
      refine ⟨126759669496961922780055753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169012892662615897040074337 126759669496961922780055753)
      ·
        refine ⟨95069752122721442085041815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126759669496961922780055753 95069752122721442085041815)
        ·
          refine ⟨142604628184082163127562723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95069752122721442085041815 142604628184082163127562723)
          ·
            refine ⟨213906942276123244691344085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142604628184082163127562723 213906942276123244691344085)
            ·
              refine ⟨5013443959596638547453377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 213906942276123244691344085 5013443959596638547453377)
              ·
                refine ⟨3760082969697478910590033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013443959596638547453377 3760082969697478910590033)
                ·
                  refine ⟨2820062227273109182942525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3760082969697478910590033 2820062227273109182942525)
                  ·
                    refine ⟨1057523335227415943603447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820062227273109182942525 1057523335227415943603447)
                    ·
                      rfl

theorem cell22_3089279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_3089279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089279 prefixEnd_3089279 := by exact prefixLift 3089279
  have htrace : WordTrace (prefixWord ++ tailWord_3089279) baseStart_3089279 baseEnd_3089279 := by
    simpa [prefixWord, tailWord_3089279, baseEnd_3089279] using wordTrace_append hprefix tailTrace_3089279
  have hstable : (prefixWord ++ tailWord_3089279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089279).length < 2 ^ (prefixWord ++ tailWord_3089279).sum := by decide
  have hdescent : baseEnd_3089279 < baseStart_3089279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089337 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 7]
def baseStart_3089337 : Nat := 118140960795 + 3089337 * 2 ^ 59
def prefixEnd_3089337 : Nat := 4983230072969 + 3 ^ 40 * 3089337 * 2
def baseEnd_3089337 : Nat := 352514396604241041884423

theorem tailTrace_3089337 : CollatzResearch.WordTrace tailWord_3089337 prefixEnd_3089337 352514396604241041884423 := by
  unfold tailWord_3089337
  simp only [CollatzResearch.WordTrace]
  refine ⟨112677377208867140598994265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75118251472578093732662843 112677377208867140598994265)
  ·
    refine ⟨84508032906650355449245699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112677377208867140598994265 84508032906650355449245699)
    ·
      refine ⟨126762049359975533173868549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84508032906650355449245699 126762049359975533173868549)
      ·
        refine ⟨23767884254995412470100353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126762049359975533173868549 23767884254995412470100353)
        ·
          refine ⟨17825913191246559352575265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23767884254995412470100353 17825913191246559352575265)
          ·
            refine ⟨13369434893434919514431449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17825913191246559352575265 13369434893434919514431449)
            ·
              refine ⟨10027076170076189635823587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13369434893434919514431449 10027076170076189635823587)
              ·
                refine ⟨15040614255114284453735381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027076170076189635823587 15040614255114284453735381)
                ·
                  refine ⟨352514396604241041884423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15040614255114284453735381 352514396604241041884423)
                  ·
                    rfl

theorem cell22_3089337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_3089337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089337 prefixEnd_3089337 := by exact prefixLift 3089337
  have htrace : WordTrace (prefixWord ++ tailWord_3089337) baseStart_3089337 baseEnd_3089337 := by
    simpa [prefixWord, tailWord_3089337, baseEnd_3089337] using wordTrace_append hprefix tailTrace_3089337
  have hstable : (prefixWord ++ tailWord_3089337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089337).length < 2 ^ (prefixWord ++ tailWord_3089337).sum := by decide
  have hdescent : baseEnd_3089337 < baseStart_3089337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089384 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3089384 : Nat := 118140960795 + 3089384 * 2 ^ 59
def prefixEnd_3089384 : Nat := 4983230072969 + 3 ^ 40 * 3089384 * 2
def baseEnd_3089384 : Nat := 1057559278873230669728125

theorem tailTrace_3089384 : CollatzResearch.WordTrace tailWord_3089384 prefixEnd_3089384 1057559278873230669728125 := by
  unfold tailWord_3089384
  simp only [CollatzResearch.WordTrace]
  refine ⟨56339545719848433812977603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75119394293131245083970137 56339545719848433812977603)
  ·
    refine ⟨84509318579772650719466405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56339545719848433812977603 84509318579772650719466405)
    ·
      refine ⟨15845497233707372009899951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84509318579772650719466405 15845497233707372009899951)
      ·
        refine ⟨23768245850561058014849927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15845497233707372009899951 23768245850561058014849927)
        ·
          refine ⟨35652368775841587022274891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23768245850561058014849927 35652368775841587022274891)
          ·
            refine ⟨53478553163762380533412337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35652368775841587022274891 53478553163762380533412337)
            ·
              refine ⟨40108914872821785400059253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53478553163762380533412337 40108914872821785400059253)
              ·
                refine ⟨3760210769327042381255555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40108914872821785400059253 3760210769327042381255555)
                ·
                  refine ⟨5640316153990563571883333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760210769327042381255555 5640316153990563571883333)
                  ·
                    refine ⟨1057559278873230669728125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640316153990563571883333 1057559278873230669728125)
                    ·
                      rfl

theorem cell22_3089384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3089384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089384 prefixEnd_3089384 := by exact prefixLift 3089384
  have htrace : WordTrace (prefixWord ++ tailWord_3089384) baseStart_3089384 baseEnd_3089384 := by
    simpa [prefixWord, tailWord_3089384, baseEnd_3089384] using wordTrace_append hprefix tailTrace_3089384
  have hstable : (prefixWord ++ tailWord_3089384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089384).length < 2 ^ (prefixWord ++ tailWord_3089384).sum := by decide
  have hdescent : baseEnd_3089384 < baseStart_3089384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089429 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 1, 6]
def baseStart_3089429 : Nat := 118140960795 + 3089429 * 2 ^ 59
def prefixEnd_3089429 : Nat := 4983230072969 + 3 ^ 40 * 3089429 * 2
def baseEnd_3089429 : Nat := 1057574683292865552352987

theorem tailTrace_3089429 : CollatzResearch.WordTrace tailWord_3089429 prefixEnd_3089429 1057574683292865552352987 := by
  unfold tailWord_3089429
  simp only [CollatzResearch.WordTrace]
  refine ⟨112680732724533840311343341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75120488483022560207562227 112680732724533840311343341)
  ·
    refine ⟨42255274771700190116753753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112680732724533840311343341 42255274771700190116753753)
    ·
      refine ⟨31691456078775142587565315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42255274771700190116753753 31691456078775142587565315)
      ·
        refine ⟨47537184118162713881347973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31691456078775142587565315 47537184118162713881347973)
        ·
          refine ⟨8913222022155508852752745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47537184118162713881347973 8913222022155508852752745)
          ·
            refine ⟨6684916516616631639564559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8913222022155508852752745 6684916516616631639564559)
            ·
              refine ⟨10027374774924947459346839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6684916516616631639564559 10027374774924947459346839)
              ·
                refine ⟨15041062162387421189020259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027374774924947459346839 15041062162387421189020259)
                ·
                  refine ⟨22561593243581131783530389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15041062162387421189020259 22561593243581131783530389)
                  ·
                    refine ⟨1057574683292865552352987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22561593243581131783530389 1057574683292865552352987)
                    ·
                      rfl

theorem cell22_3089429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_3089429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089429 prefixEnd_3089429 := by exact prefixLift 3089429
  have htrace : WordTrace (prefixWord ++ tailWord_3089429) baseStart_3089429 baseEnd_3089429 := by
    simpa [prefixWord, tailWord_3089429, baseEnd_3089429] using wordTrace_append hprefix tailTrace_3089429
  have hstable : (prefixWord ++ tailWord_3089429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089429).length < 2 ^ (prefixWord ++ tailWord_3089429).sum := by decide
  have hdescent : baseEnd_3089429 < baseStart_3089429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089444 : List Nat := [2, 3, 1, 4, 1, 2, 9]
def baseStart_3089444 : Nat := 118140960795 + 3089444 * 2 ^ 59
def prefixEnd_3089444 : Nat := 4983230072969 + 3 ^ 40 * 3089444 * 2
def baseEnd_3089444 : Nat := 39169622892570759749183

theorem tailTrace_3089444 : CollatzResearch.WordTrace tailWord_3089444 prefixEnd_3089444 39169622892570759749183 := by
  unfold tailWord_3089444
  simp only [CollatzResearch.WordTrace]
  refine ⟨56340639909739748936569693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75120853212986331915426257 56340639909739748936569693)
  ·
    refine ⟨21127739966152405851213635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56340639909739748936569693 21127739966152405851213635)
    ·
      refine ⟨31691609949228608776820453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21127739966152405851213635 31691609949228608776820453)
      ·
        refine ⟨5942176865480364145653835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31691609949228608776820453 5942176865480364145653835)
        ·
          refine ⟨8913265298220546218480753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942176865480364145653835 8913265298220546218480753)
          ·
            refine ⟨6684948973665409663860565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8913265298220546218480753 6684948973665409663860565)
            ·
              refine ⟨39169622892570759749183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6684948973665409663860565 39169622892570759749183)
              ·
                rfl

theorem cell22_3089444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 9].length) (baseStart_3089444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089444 prefixEnd_3089444 := by exact prefixLift 3089444
  have htrace : WordTrace (prefixWord ++ tailWord_3089444) baseStart_3089444 baseEnd_3089444 := by
    simpa [prefixWord, tailWord_3089444, baseEnd_3089444] using wordTrace_append hprefix tailTrace_3089444
  have hstable : (prefixWord ++ tailWord_3089444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089444).length < 2 ^ (prefixWord ++ tailWord_3089444).sum := by decide
  have hdescent : baseEnd_3089444 < baseStart_3089444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089478 : List Nat := [6, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3089478 : Nat := 118140960795 + 3089478 * 2 ^ 59
def prefixEnd_3089478 : Nat := 4983230072969 + 3 ^ 40 * 3089478 * 2
def baseEnd_3089478 : Nat := 117510161888249528653093

theorem tailTrace_3089478 : CollatzResearch.WordTrace tailWord_3089478 prefixEnd_3089478 117510161888249528653093 := by
  unfold tailWord_3089478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3521328746917385052496159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75121679934237547786584725 3521328746917385052496159)
  ·
    refine ⟨5281993120376077578744239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3521328746917385052496159 5281993120376077578744239)
    ·
      refine ⟨7922989680564116368116359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5281993120376077578744239 7922989680564116368116359)
      ·
        refine ⟨11884484520846174552174539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7922989680564116368116359 11884484520846174552174539)
        ·
          refine ⟨17826726781269261828261809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11884484520846174552174539 17826726781269261828261809)
          ·
            refine ⟨13370045085951946371196357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17826726781269261828261809 13370045085951946371196357)
            ·
              refine ⟨2506883453615989944599317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13370045085951946371196357 2506883453615989944599317)
              ·
                refine ⟨117510161888249528653093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2506883453615989944599317 117510161888249528653093)
                ·
                  rfl

theorem cell22_3089478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3089478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089478 prefixEnd_3089478 := by exact prefixLift 3089478
  have htrace : WordTrace (prefixWord ++ tailWord_3089478) baseStart_3089478 baseEnd_3089478 := by
    simpa [prefixWord, tailWord_3089478, baseEnd_3089478] using wordTrace_append hprefix tailTrace_3089478
  have hstable : (prefixWord ++ tailWord_3089478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089478).length < 2 ^ (prefixWord ++ tailWord_3089478).sum := by decide
  have hdescent : baseEnd_3089478 < baseStart_3089478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089506 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3089506 : Nat := 118140960795 + 3089506 * 2 ^ 59
def prefixEnd_3089506 : Nat := 4983230072969 + 3 ^ 40 * 3089506 * 2
def baseEnd_3089506 : Nat := 352533680655487672725917

theorem tailTrace_3089506 : CollatzResearch.WordTrace tailWord_3089506 prefixEnd_3089506 352533680655487672725917 := by
  unfold tailWord_3089506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28170885286313720615474093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75122360763503254974597581 28170885286313720615474093)
  ·
    refine ⟨10564081982367645230802785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28170885286313720615474093 10564081982367645230802785)
    ·
      refine ⟨7923061486775733923102089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10564081982367645230802785 7923061486775733923102089)
      ·
        refine ⟨5942296115081800442326567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7923061486775733923102089 5942296115081800442326567)
        ·
          refine ⟨8913444172622700663489851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5942296115081800442326567 8913444172622700663489851)
          ·
            refine ⟨13370166258934050995234777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913444172622700663489851 13370166258934050995234777)
            ·
              refine ⟨10027624694200538246426083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13370166258934050995234777 10027624694200538246426083)
              ·
                refine ⟨15041437041300807369639125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10027624694200538246426083 15041437041300807369639125)
                ·
                  refine ⟨352533680655487672725917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15041437041300807369639125 352533680655487672725917)
                  ·
                    rfl

theorem cell22_3089506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3089506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089506 prefixEnd_3089506 := by exact prefixLift 3089506
  have htrace : WordTrace (prefixWord ++ tailWord_3089506) baseStart_3089506 baseEnd_3089506 := by
    simpa [prefixWord, tailWord_3089506, baseEnd_3089506] using wordTrace_append hprefix tailTrace_3089506
  have hstable : (prefixWord ++ tailWord_3089506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089506).length < 2 ^ (prefixWord ++ tailWord_3089506).sum := by decide
  have hdescent : baseEnd_3089506 < baseStart_3089506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089519 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 3, 4]
def baseStart_3089519 : Nat := 118140960795 + 3089519 * 2 ^ 59
def prefixEnd_3089519 : Nat := 4983230072969 + 3 ^ 40 * 3089519 * 2
def baseEnd_3089519 : Nat := 1057605492132135317602711

theorem tailTrace_3089519 : CollatzResearch.WordTrace tailWord_3089519 prefixEnd_3089519 1057605492132135317602711 := by
  unfold tailWord_3089519
  simp only [CollatzResearch.WordTrace]
  refine ⟨112684015294207785682119611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75122676862805190454746407 112684015294207785682119611)
  ·
    refine ⟨169026022941311678523179417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112684015294207785682119611 169026022941311678523179417)
    ·
      refine ⟨126769517205983758892384563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169026022941311678523179417 126769517205983758892384563)
      ·
        refine ⟨190154275808975638338576845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126769517205983758892384563 190154275808975638338576845)
        ·
          refine ⟨71307853428365864376966317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190154275808975638338576845 71307853428365864376966317)
          ·
            refine ⟨26740445035637199141362369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71307853428365864376966317 26740445035637199141362369)
            ·
              refine ⟨20055333776727899356021777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26740445035637199141362369 20055333776727899356021777)
              ·
                refine ⟨15041500332545924517016333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20055333776727899356021777 15041500332545924517016333)
                ·
                  refine ⟨5640562624704721693881125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15041500332545924517016333 5640562624704721693881125)
                  ·
                    refine ⟨1057605492132135317602711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640562624704721693881125 1057605492132135317602711)
                    ·
                      rfl

theorem cell22_3089519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_3089519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089519 prefixEnd_3089519 := by exact prefixLift 3089519
  have htrace : WordTrace (prefixWord ++ tailWord_3089519) baseStart_3089519 baseEnd_3089519 := by
    simpa [prefixWord, tailWord_3089519, baseEnd_3089519] using wordTrace_append hprefix tailTrace_3089519
  have hstable : (prefixWord ++ tailWord_3089519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089519).length < 2 ^ (prefixWord ++ tailWord_3089519).sum := by decide
  have hdescent : baseEnd_3089519 < baseStart_3089519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089536 : List Nat := [2, 1, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_3089536 : Nat := 118140960795 + 3089536 * 2 ^ 59
def prefixEnd_3089536 : Nat := 4983230072969 + 3 ^ 40 * 3089536 * 2
def baseEnd_3089536 : Nat := 1057611311579552939927659

theorem tailTrace_3089536 : CollatzResearch.WordTrace tailWord_3089536 prefixEnd_3089536 1057611311579552939927659 := by
  unfold tailWord_3089536
  simp only [CollatzResearch.WordTrace]
  refine ⟨56342317667573098792744231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75123090223430798390325641 56342317667573098792744231)
  ·
    refine ⟨84513476501359648189116347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56342317667573098792744231 84513476501359648189116347)
    ·
      refine ⟨126770214752039472283674521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84513476501359648189116347 126770214752039472283674521)
      ·
        refine ⟨95077661064029604212755891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126770214752039472283674521 95077661064029604212755891)
        ·
          refine ⟨142616491596044406319133837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95077661064029604212755891 142616491596044406319133837)
          ·
            refine ⟨53481184348516652369675189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142616491596044406319133837 53481184348516652369675189)
            ·
              refine ⟨5013861032673436159657049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53481184348516652369675189 5013861032673436159657049)
              ·
                refine ⟨3760395774505077119742787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5013861032673436159657049 3760395774505077119742787)
                ·
                  refine ⟨5640593661757615679614181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3760395774505077119742787 5640593661757615679614181)
                  ·
                    refine ⟨1057611311579552939927659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640593661757615679614181 1057611311579552939927659)
                    ·
                      rfl

theorem cell22_3089536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_3089536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089536 prefixEnd_3089536 := by exact prefixLift 3089536
  have htrace : WordTrace (prefixWord ++ tailWord_3089536) baseStart_3089536 baseEnd_3089536 := by
    simpa [prefixWord, tailWord_3089536, baseEnd_3089536] using wordTrace_append hprefix tailTrace_3089536
  have hstable : (prefixWord ++ tailWord_3089536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089536).length < 2 ^ (prefixWord ++ tailWord_3089536).sum := by decide
  have hdescent : baseEnd_3089536 < baseStart_3089536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089598 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_3089598 : Nat := 118140960795 + 3089598 * 2 ^ 59
def prefixEnd_3089598 : Nat := 4983230072969 + 3 ^ 40 * 3089598 * 2
def baseEnd_3089598 : Nat := 1057632535446605444877469

theorem tailTrace_3089598 : CollatzResearch.WordTrace tailWord_3089598 prefixEnd_3089598 1057632535446605444877469 := by
  unfold tailWord_3089598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14085862082615197771780681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75124597773947721449496965 14085862082615197771780681)
  ·
    refine ⟨10564396561961398328835511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14085862082615197771780681 10564396561961398328835511)
    ·
      refine ⟨15846594842942097493253267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10564396561961398328835511 15846594842942097493253267)
      ·
        refine ⟨23769892264413146239879901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15846594842942097493253267 23769892264413146239879901)
        ·
          refine ⟨8913709599154929839954963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23769892264413146239879901 8913709599154929839954963)
          ·
            refine ⟨13370564398732394759932445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8913709599154929839954963 13370564398732394759932445)
            ·
              refine ⟨5013961649524648034974667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13370564398732394759932445 5013961649524648034974667)
              ·
                refine ⟨7520942474286972052462001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013961649524648034974667 7520942474286972052462001)
                ·
                  refine ⟨5640706855715229039346501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7520942474286972052462001 5640706855715229039346501)
                  ·
                    refine ⟨1057632535446605444877469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5640706855715229039346501 1057632535446605444877469)
                    ·
                      rfl

theorem cell22_3089598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_3089598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089598 prefixEnd_3089598 := by exact prefixLift 3089598
  have htrace : WordTrace (prefixWord ++ tailWord_3089598) baseStart_3089598 baseEnd_3089598 := by
    simpa [prefixWord, tailWord_3089598, baseEnd_3089598] using wordTrace_append hprefix tailTrace_3089598
  have hstable : (prefixWord ++ tailWord_3089598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089598).length < 2 ^ (prefixWord ++ tailWord_3089598).sum := by decide
  have hdescent : baseEnd_3089598 < baseStart_3089598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089662 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_3089662 : Nat := 118140960795 + 3089662 * 2 ^ 59
def prefixEnd_3089662 : Nat := 4983230072969 + 3 ^ 40 * 3089662 * 2
def baseEnd_3089662 : Nat := 1057654443954530611277273

theorem tailTrace_3089662 : CollatzResearch.WordTrace tailWord_3089662 prefixEnd_3089662 1057654443954530611277273 := by
  unfold tailWord_3089662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14086153866586215138071905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75126153955126480736383493 14086153866586215138071905)
  ·
    refine ⟨10564615399939661353553929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14086153866586215138071905 10564615399939661353553929)
    ·
      refine ⟨7923461549954746015165447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10564615399939661353553929 7923461549954746015165447)
      ·
        refine ⟨11885192324932119022748171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7923461549954746015165447 11885192324932119022748171)
        ·
          refine ⟨17827788487398178534122257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11885192324932119022748171 17827788487398178534122257)
          ·
            refine ⟨13370841365548633900591693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17827788487398178534122257 13370841365548633900591693)
            ·
              refine ⟨5014065512080737712721885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13370841365548633900591693 5014065512080737712721885)
              ·
                refine ⟨1880274567030276642270707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014065512080737712721885 1880274567030276642270707)
                ·
                  refine ⟨2820411850545414963406061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880274567030276642270707 2820411850545414963406061)
                  ·
                    refine ⟨1057654443954530611277273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820411850545414963406061 1057654443954530611277273)
                    ·
                      rfl

theorem cell22_3089662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_3089662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089662 prefixEnd_3089662 := by exact prefixLift 3089662
  have htrace : WordTrace (prefixWord ++ tailWord_3089662) baseStart_3089662 baseEnd_3089662 := by
    simpa [prefixWord, tailWord_3089662, baseEnd_3089662] using wordTrace_append hprefix tailTrace_3089662
  have hstable : (prefixWord ++ tailWord_3089662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089662).length < 2 ^ (prefixWord ++ tailWord_3089662).sum := by decide
  have hdescent : baseEnd_3089662 < baseStart_3089662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089735 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 2, 3]
def baseStart_3089735 : Nat := 118140960795 + 3089735 * 2 ^ 59
def prefixEnd_3089735 : Nat := 4983230072969 + 3 ^ 40 * 3089735 * 2
def baseEnd_3089735 : Nat := 1057679433346382754202049

theorem tailTrace_3089735 : CollatzResearch.WordTrace tailWord_3089735 prefixEnd_3089735 1057679433346382754202049 := by
  unfold tailWord_3089735
  simp only [CollatzResearch.WordTrace]
  refine ⟨112691893461425254571982659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75127928974283503047988439 112691893461425254571982659)
  ·
    refine ⟨169037840192137881857973989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112691893461425254571982659 169037840192137881857973989)
    ·
      refine ⟨31694595036025852848370123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169037840192137881857973989 31694595036025852848370123)
      ·
        refine ⟨47541892554038779272555185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31694595036025852848370123 47541892554038779272555185)
        ·
          refine ⟨35656419415529084454416389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47541892554038779272555185 35656419415529084454416389)
          ·
            refine ⟨6685578640411703335203073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35656419415529084454416389 6685578640411703335203073)
            ·
              refine ⟨5014183980308777501402305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6685578640411703335203073 5014183980308777501402305)
              ·
                refine ⟨3760637985231583126051729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5014183980308777501402305 3760637985231583126051729)
                ·
                  refine ⟨2820478488923687344538797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3760637985231583126051729 2820478488923687344538797)
                  ·
                    refine ⟨1057679433346382754202049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820478488923687344538797 1057679433346382754202049)
                    ·
                      rfl

theorem cell22_3089735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_3089735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089735 prefixEnd_3089735 := by exact prefixLift 3089735
  have htrace : WordTrace (prefixWord ++ tailWord_3089735) baseStart_3089735 baseEnd_3089735 := by
    simpa [prefixWord, tailWord_3089735, baseEnd_3089735] using wordTrace_append hprefix tailTrace_3089735
  have hstable : (prefixWord ++ tailWord_3089735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089735).length < 2 ^ (prefixWord ++ tailWord_3089735).sum := by decide
  have hdescent : baseEnd_3089735 < baseStart_3089735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089746 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3089746 : Nat := 118140960795 + 3089746 * 2 ^ 59
def prefixEnd_3089746 : Nat := 4983230072969 + 3 ^ 40 * 3089746 * 2
def baseEnd_3089746 : Nat := 1057683198871182392177015

theorem tailTrace_3089746 : CollatzResearch.WordTrace tailWord_3089746 prefixEnd_3089746 1057683198871182392177015 := by
  unfold tailWord_3089746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28173073666096350862658273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75128196442923602300422061 28173073666096350862658273)
  ·
    refine ⟨21129805249572263146993705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28173073666096350862658273 21129805249572263146993705)
    ·
      refine ⟨15847353937179197360245279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21129805249572263146993705 15847353937179197360245279)
      ·
        refine ⟨23771030905768796040367919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15847353937179197360245279 23771030905768796040367919)
        ·
          refine ⟨35656546358653194060551879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23771030905768796040367919 35656546358653194060551879)
          ·
            refine ⟨53484819537979791090827819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35656546358653194060551879 53484819537979791090827819)
            ·
              refine ⟨80227229306969686636241729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53484819537979791090827819 80227229306969686636241729)
              ·
                refine ⟨60170421980227264977181297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80227229306969686636241729 60170421980227264977181297)
                ·
                  refine ⟨45127816485170448732885973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60170421980227264977181297 45127816485170448732885973)
                  ·
                    refine ⟨1057683198871182392177015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45127816485170448732885973 1057683198871182392177015)
                    ·
                      rfl

theorem cell22_3089746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3089746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089746 prefixEnd_3089746 := by exact prefixLift 3089746
  have htrace : WordTrace (prefixWord ++ tailWord_3089746) baseStart_3089746 baseEnd_3089746 := by
    simpa [prefixWord, tailWord_3089746, baseEnd_3089746] using wordTrace_append hprefix tailTrace_3089746
  have hstable : (prefixWord ++ tailWord_3089746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089746).length < 2 ^ (prefixWord ++ tailWord_3089746).sum := by decide
  have hdescent : baseEnd_3089746 < baseStart_3089746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089763 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 5, 3]
def baseStart_3089763 : Nat := 118140960795 + 3089763 * 2 ^ 59
def prefixEnd_3089763 : Nat := 4983230072969 + 3 ^ 40 * 3089763 * 2
def baseEnd_3089763 : Nat := 1057689018318600014501963

theorem tailTrace_3089763 : CollatzResearch.WordTrace tailWord_3089763 prefixEnd_3089763 1057689018318600014501963 := by
  unfold tailWord_3089763
  simp only [CollatzResearch.WordTrace]
  refine ⟨112692914705323815354001943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75128609803549210236001295 112692914705323815354001943)
  ·
    refine ⟨169039372057985723031002915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112692914705323815354001943 169039372057985723031002915)
    ·
      refine ⟨253559058086978584546504373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169039372057985723031002915 253559058086978584546504373)
      ·
        refine ⟨23771161695654242301234785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 253559058086978584546504373 23771161695654242301234785)
        ·
          refine ⟨17828371271740681725926089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23771161695654242301234785 17828371271740681725926089)
          ·
            refine ⟨13371278453805511294444567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17828371271740681725926089 13371278453805511294444567)
            ·
              refine ⟨20056917680708266941666851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13371278453805511294444567 20056917680708266941666851)
              ·
                refine ⟨30085376521062400412500277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20056917680708266941666851 30085376521062400412500277)
                ·
                  refine ⟨2820504048849600038671901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30085376521062400412500277 2820504048849600038671901)
                  ·
                    refine ⟨1057689018318600014501963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820504048849600038671901 1057689018318600014501963)
                    ·
                      rfl

theorem cell22_3089763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 5, 3].length) (baseStart_3089763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089763 prefixEnd_3089763 := by exact prefixLift 3089763
  have htrace : WordTrace (prefixWord ++ tailWord_3089763) baseStart_3089763 baseEnd_3089763 := by
    simpa [prefixWord, tailWord_3089763, baseEnd_3089763] using wordTrace_append hprefix tailTrace_3089763
  have hstable : (prefixWord ++ tailWord_3089763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089763).length < 2 ^ (prefixWord ++ tailWord_3089763).sum := by decide
  have hdescent : baseEnd_3089763 < baseStart_3089763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089767 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3089767 : Nat := 118140960795 + 3089767 * 2 ^ 59
def prefixEnd_3089767 : Nat := 4983230072969 + 3 ^ 40 * 3089767 * 2
def baseEnd_3089767 : Nat := 1057690387600345337401951

theorem tailTrace_3089767 : CollatzResearch.WordTrace tailWord_3089767 prefixEnd_3089767 1057690387600345337401951 := by
  unfold tailWord_3089767
  simp only [CollatzResearch.WordTrace]
  refine ⟨112693060597309324037147555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75128707064872882691431703 112693060597309324037147555)
  ·
    refine ⟨169039590895963986055721333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112693060597309324037147555 169039590895963986055721333)
    ·
      refine ⟨15847461646496623692723875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169039590895963986055721333 15847461646496623692723875)
      ·
        refine ⟨23771192469744935539085813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15847461646496623692723875 23771192469744935539085813)
        ·
          refine ⟨2228549294038587706789295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23771192469744935539085813 2228549294038587706789295)
          ·
            refine ⟨3342823941057881560183943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2228549294038587706789295 3342823941057881560183943)
            ·
              refine ⟨5014235911586822340275915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342823941057881560183943 5014235911586822340275915)
              ·
                refine ⟨7521353867380233510413873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5014235911586822340275915 7521353867380233510413873)
                ·
                  refine ⟨5641015400535175132810405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7521353867380233510413873 5641015400535175132810405)
                  ·
                    refine ⟨1057690387600345337401951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641015400535175132810405 1057690387600345337401951)
                    ·
                      rfl

theorem cell22_3089767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3089767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089767 prefixEnd_3089767 := by exact prefixLift 3089767
  have htrace : WordTrace (prefixWord ++ tailWord_3089767) baseStart_3089767 baseEnd_3089767 := by
    simpa [prefixWord, tailWord_3089767, baseEnd_3089767] using wordTrace_append hprefix tailTrace_3089767
  have hstable : (prefixWord ++ tailWord_3089767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089767).length < 2 ^ (prefixWord ++ tailWord_3089767).sum := by decide
  have hdescent : baseEnd_3089767 < baseStart_3089767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089776 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 7]
def baseStart_3089776 : Nat := 118140960795 + 3089776 * 2 ^ 59
def prefixEnd_3089776 : Nat := 4983230072969 + 3 ^ 40 * 3089776 * 2
def baseEnd_3089776 : Nat := 352564489494757437975641

theorem tailTrace_3089776 : CollatzResearch.WordTrace tailWord_3089776 prefixEnd_3089776 352564489494757437975641 := by
  unfold tailWord_3089776
  simp only [CollatzResearch.WordTrace]
  refine ⟨56346694427138359287112591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75128925902851145716150121 56346694427138359287112591)
  ·
    refine ⟨84520041640707538930668887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56346694427138359287112591 84520041640707538930668887)
    ·
      refine ⟨126780062461061308396003331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84520041640707538930668887 126780062461061308396003331)
      ·
        refine ⟨190170093691591962594004997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126780062461061308396003331 190170093691591962594004997)
        ·
          refine ⟨35656892567173492986375937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190170093691591962594004997 35656892567173492986375937)
          ·
            refine ⟨26742669425380119739781953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35656892567173492986375937 26742669425380119739781953)
            ·
              refine ⟨20057002069035089804836465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26742669425380119739781953 20057002069035089804836465)
              ·
                refine ⟨15042751551776317353627349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20057002069035089804836465 15042751551776317353627349)
                ·
                  refine ⟨352564489494757437975641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15042751551776317353627349 352564489494757437975641)
                  ·
                    rfl

theorem cell22_3089776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_3089776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089776 prefixEnd_3089776 := by exact prefixLift 3089776
  have htrace : WordTrace (prefixWord ++ tailWord_3089776) baseStart_3089776 baseEnd_3089776 := by
    simpa [prefixWord, tailWord_3089776, baseEnd_3089776] using wordTrace_append hprefix tailTrace_3089776
  have hstable : (prefixWord ++ tailWord_3089776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089776).length < 2 ^ (prefixWord ++ tailWord_3089776).sum := by decide
  have hdescent : baseEnd_3089776 < baseStart_3089776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089885 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3089885 : Nat := 118140960795 + 3089885 * 2 ^ 59
def prefixEnd_3089885 : Nat := 4983230072969 + 3 ^ 40 * 3089885 * 2
def baseEnd_3089885 : Nat := 1057730781411832362951589

theorem tailTrace_3089885 : CollatzResearch.WordTrace tailWord_3089885 prefixEnd_3089885 1057730781411832362951589 := by
  unfold tailWord_3089885
  simp only [CollatzResearch.WordTrace]
  refine ⟨112697364410881830189943109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75131576273921220126628739 112697364410881830189943109)
  ·
    refine ⟨21130755827040343160614333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112697364410881830189943109 21130755827040343160614333)
    ·
      refine ⟨7924033435140128685230375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21130755827040343160614333 7924033435140128685230375)
      ·
        refine ⟨11886050152710193027845563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7924033435140128685230375 11886050152710193027845563)
        ·
          refine ⟨17829075229065289541768345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11886050152710193027845563 17829075229065289541768345)
          ·
            refine ⟨13371806421798967156326259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17829075229065289541768345 13371806421798967156326259)
            ·
              refine ⟨20057709632698450734489389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13371806421798967156326259 20057709632698450734489389)
              ·
                refine ⟨7521641112261919025433521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20057709632698450734489389 7521641112261919025433521)
                ·
                  refine ⟨5641230834196439269075141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7521641112261919025433521 5641230834196439269075141)
                  ·
                    refine ⟨1057730781411832362951589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641230834196439269075141 1057730781411832362951589)
                    ·
                      rfl

theorem cell22_3089885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3089885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089885 prefixEnd_3089885 := by exact prefixLift 3089885
  have htrace : WordTrace (prefixWord ++ tailWord_3089885) baseStart_3089885 baseEnd_3089885 := by
    simpa [prefixWord, tailWord_3089885, baseEnd_3089885] using wordTrace_append hprefix tailTrace_3089885
  have hstable : (prefixWord ++ tailWord_3089885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089885).length < 2 ^ (prefixWord ++ tailWord_3089885).sum := by decide
  have hdescent : baseEnd_3089885 < baseStart_3089885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089932 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_3089932 : Nat := 118140960795 + 3089932 * 2 ^ 59
def prefixEnd_3089932 : Nat := 4983230072969 + 3 ^ 40 * 3089932 * 2
def baseEnd_3089932 : Nat := 1057746870472339907026445

theorem tailTrace_3089932 : CollatzResearch.WordTrace tailWord_3089932 prefixEnd_3089932 1057746870472339907026445 := by
  unfold tailWord_3089932
  simp only [CollatzResearch.WordTrace]
  refine ⟨56349539320855778608452025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75132719094474371477936033 56349539320855778608452025)
  ·
    refine ⟨42262154490641833956339019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56349539320855778608452025 42262154490641833956339019)
    ·
      refine ⟨63393231735962750934508529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42262154490641833956339019 63393231735962750934508529)
      ·
        refine ⟨47544923801972063200881397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63393231735962750934508529 47544923801972063200881397)
        ·
          refine ⟨4457336606434880925082631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47544923801972063200881397 4457336606434880925082631)
          ·
            refine ⟨6686004909652321387623947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4457336606434880925082631 6686004909652321387623947)
            ·
              refine ⟨10029007364478482081435921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6686004909652321387623947 10029007364478482081435921)
              ·
                refine ⟨7521755523358861561076941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10029007364478482081435921 7521755523358861561076941)
                ·
                  refine ⟨2820658321259573085403853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7521755523358861561076941 2820658321259573085403853)
                  ·
                    refine ⟨1057746870472339907026445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820658321259573085403853 1057746870472339907026445)
                    ·
                      rfl

theorem cell22_3089932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_3089932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089932 prefixEnd_3089932 := by exact prefixLift 3089932
  have htrace : WordTrace (prefixWord ++ tailWord_3089932) baseStart_3089932 baseEnd_3089932 := by
    simpa [prefixWord, tailWord_3089932, baseEnd_3089932] using wordTrace_append hprefix tailTrace_3089932
  have hstable : (prefixWord ++ tailWord_3089932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089932).length < 2 ^ (prefixWord ++ tailWord_3089932).sum := by decide
  have hdescent : baseEnd_3089932 < baseStart_3089932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3089949 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3089949 : Nat := 118140960795 + 3089949 * 2 ^ 59
def prefixEnd_3089949 : Nat := 4983230072969 + 3 ^ 40 * 3089949 * 2
def baseEnd_3089949 : Nat := 1057752689919757529351393

theorem tailTrace_3089949 : CollatzResearch.WordTrace tailWord_3089949 prefixEnd_3089949 1057752689919757529351393 := by
  unfold tailWord_3089949
  simp only [CollatzResearch.WordTrace]
  refine ⟨112699698682649969120272901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75133132455099979413515267 112699698682649969120272901)
  ·
    refine ⟨21131193502996869210051169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112699698682649969120272901 21131193502996869210051169)
    ·
      refine ⟨15848395127247651907538377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21131193502996869210051169 15848395127247651907538377)
      ·
        refine ⟨11886296345435738930653783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15848395127247651907538377 11886296345435738930653783)
        ·
          refine ⟨17829444518153608395980675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11886296345435738930653783 17829444518153608395980675)
          ·
            refine ⟨26744166777230412593971013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17829444518153608395980675 26744166777230412593971013)
            ·
              refine ⟨5014531270730702361369565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26744166777230412593971013 5014531270730702361369565)
              ·
                refine ⟨1880449226524013385513587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014531270730702361369565 1880449226524013385513587)
                ·
                  refine ⟨2820673839786020078270381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880449226524013385513587 2820673839786020078270381)
                  ·
                    refine ⟨1057752689919757529351393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2820673839786020078270381 1057752689919757529351393)
                    ·
                      rfl

theorem cell22_3089949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3089949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3089949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3089949 prefixEnd_3089949 := by exact prefixLift 3089949
  have htrace : WordTrace (prefixWord ++ tailWord_3089949) baseStart_3089949 baseEnd_3089949 := by
    simpa [prefixWord, tailWord_3089949, baseEnd_3089949] using wordTrace_append hprefix tailTrace_3089949
  have hstable : (prefixWord ++ tailWord_3089949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3089949).length < 2 ^ (prefixWord ++ tailWord_3089949).sum := by decide
  have hdescent : baseEnd_3089949 < baseStart_3089949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3089949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090007 : List Nat := [1, 1, 3, 2, 2, 3, 3, 3, 4]
def baseStart_3090007 : Nat := 118140960795 + 3090007 * 2 ^ 59
def prefixEnd_3090007 : Nat := 4983230072969 + 3 ^ 40 * 3090007 * 2
def baseEnd_3090007 : Nat := 352590848168354903800405

theorem tailTrace_3090007 : CollatzResearch.WordTrace tailWord_3090007 prefixEnd_3090007 352590848168354903800405 := by
  unfold tailWord_3090007
  simp only [CollatzResearch.WordTrace]
  refine ⟨112701814116439845025884275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75134542744293230017256183 112701814116439845025884275)
  ·
    refine ⟨169052721174659767538826413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112701814116439845025884275 169052721174659767538826413)
    ·
      refine ⟨63394770440497412827059905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169052721174659767538826413 63394770440497412827059905)
      ·
        refine ⟨47546077830373059620294929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63394770440497412827059905 47546077830373059620294929)
        ·
          refine ⟨35659558372779794715221197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47546077830373059620294929 35659558372779794715221197)
          ·
            refine ⟨13372334389792423018207949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35659558372779794715221197 13372334389792423018207949)
            ·
              refine ⟨5014625396172158631827981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13372334389792423018207949 5014625396172158631827981)
              ·
                refine ⟨1880484523564559486935493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5014625396172158631827981 1880484523564559486935493)
                ·
                  refine ⟨352590848168354903800405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1880484523564559486935493 352590848168354903800405)
                  ·
                    rfl

theorem cell22_3090007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3, 4].length) (baseStart_3090007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090007 prefixEnd_3090007 := by exact prefixLift 3090007
  have htrace : WordTrace (prefixWord ++ tailWord_3090007) baseStart_3090007 baseEnd_3090007 := by
    simpa [prefixWord, tailWord_3090007, baseEnd_3090007] using wordTrace_append hprefix tailTrace_3090007
  have hstable : (prefixWord ++ tailWord_3090007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090007).length < 2 ^ (prefixWord ++ tailWord_3090007).sum := by decide
  have hdescent : baseEnd_3090007 < baseStart_3090007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090020 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_3090020 : Nat := 118140960795 + 3090020 * 2 ^ 59
def prefixEnd_3090020 : Nat := 4983230072969 + 3 ^ 40 * 3090020 * 2
def baseEnd_3090020 : Nat := 1057776994670737010826175

theorem tailTrace_3090020 : CollatzResearch.WordTrace tailWord_3090020 prefixEnd_3090020 1057776994670737010826175 := by
  unfold tailWord_3090020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56351144132696374123053757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75134858843595165497405009 56351144132696374123053757)
  ·
    refine ⟨21131679049761140296145159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56351144132696374123053757 21131679049761140296145159)
    ·
      refine ⟨31697518574641710444217739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21131679049761140296145159 31697518574641710444217739)
      ·
        refine ⟨47546277861962565666326609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31697518574641710444217739 47546277861962565666326609)
        ·
          refine ⟨35659708396471924249744957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47546277861962565666326609 35659708396471924249744957)
          ·
            refine ⟨13372390648676971593654359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35659708396471924249744957 13372390648676971593654359)
            ·
              refine ⟨20058585973015457390481539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13372390648676971593654359 20058585973015457390481539)
              ·
                refine ⟨30087878959523186085722309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20058585973015457390481539 30087878959523186085722309)
                ·
                  refine ⟨5641477304910597391072933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30087878959523186085722309 5641477304910597391072933)
                  ·
                    refine ⟨1057776994670737010826175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641477304910597391072933 1057776994670737010826175)
                    ·
                      rfl

theorem cell22_3090020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_3090020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090020 prefixEnd_3090020 := by exact prefixLift 3090020
  have htrace : WordTrace (prefixWord ++ tailWord_3090020) baseStart_3090020 baseEnd_3090020 := by
    simpa [prefixWord, tailWord_3090020, baseEnd_3090020] using wordTrace_append hprefix tailTrace_3090020
  have hstable : (prefixWord ++ tailWord_3090020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090020).length < 2 ^ (prefixWord ++ tailWord_3090020).sum := by decide
  have hdescent : baseEnd_3090020 < baseStart_3090020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090095 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 2, 5]
def baseStart_3090095 : Nat := 118140960795 + 3090095 * 2 ^ 59
def prefixEnd_3090095 : Nat := 4983230072969 + 3 ^ 40 * 3090095 * 2
def baseEnd_3090095 : Nat := 1057802668703461815200945

theorem tailTrace_3090095 : CollatzResearch.WordTrace tailWord_3090095 prefixEnd_3090095 1057802668703461815200945 := by
  unfold tailWord_3090095
  simp only [CollatzResearch.WordTrace]
  refine ⟨112705023740121036055087739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75136682493414024036725159 112705023740121036055087739)
  ·
    refine ⟨169057535610181554082631609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112705023740121036055087739 169057535610181554082631609)
    ·
      refine ⟨126793151707636165561973707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169057535610181554082631609 126793151707636165561973707)
      ·
        refine ⟨190189727561454248342960561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126793151707636165561973707 190189727561454248342960561)
        ·
          refine ⟨142642295671090686257220421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190189727561454248342960561 142642295671090686257220421)
          ·
            refine ⟨26745430438329503673228829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142642295671090686257220421 26745430438329503673228829)
            ·
              refine ⟨10029536414373563877460811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26745430438329503673228829 10029536414373563877460811)
              ·
                refine ⟨15044304621560345816191217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10029536414373563877460811 15044304621560345816191217)
                ·
                  refine ⟨11283228466170259362143413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15044304621560345816191217 11283228466170259362143413)
                  ·
                    refine ⟨1057802668703461815200945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11283228466170259362143413 1057802668703461815200945)
                    ·
                      rfl

theorem cell22_3090095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_3090095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090095 prefixEnd_3090095 := by exact prefixLift 3090095
  have htrace : WordTrace (prefixWord ++ tailWord_3090095) baseStart_3090095 baseEnd_3090095 := by
    simpa [prefixWord, tailWord_3090095, baseEnd_3090095] using wordTrace_append hprefix tailTrace_3090095
  have hstable : (prefixWord ++ tailWord_3090095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090095).length < 2 ^ (prefixWord ++ tailWord_3090095).sum := by decide
  have hdescent : baseEnd_3090095 < baseStart_3090095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090155 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_3090155 : Nat := 118140960795 + 3090155 * 2 ^ 59
def prefixEnd_3090155 : Nat := 4983230072969 + 3 ^ 40 * 3090155 * 2
def baseEnd_3090155 : Nat := 1057823207929641658700761

theorem tailTrace_3090155 : CollatzResearch.WordTrace tailWord_3090155 prefixEnd_3090155 1057823207929641658700761 := by
  unfold tailWord_3090155
  simp only [CollatzResearch.WordTrace]
  refine ⟨112707212119903666302271919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75138141413269110868181279 112707212119903666302271919)
  ·
    refine ⟨169060818179855499453407879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112707212119903666302271919 169060818179855499453407879)
    ·
      refine ⟨253591227269783249180111819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169060818179855499453407879 253591227269783249180111819)
      ·
        refine ⟨380386840904674873770167729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253591227269783249180111819 380386840904674873770167729)
        ·
          refine ⟨285290130678506155327625797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380386840904674873770167729 285290130678506155327625797)
          ·
            refine ⟨53491899502219904123929837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285290130678506155327625797 53491899502219904123929837)
            ·
              refine ⟨20059462313332464046473689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53491899502219904123929837 20059462313332464046473689)
              ·
                refine ⟨15044596734999348034855267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20059462313332464046473689 15044596734999348034855267)
                ·
                  refine ⟨22566895102499022052282901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15044596734999348034855267 22566895102499022052282901)
                  ·
                    refine ⟨1057823207929641658700761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22566895102499022052282901 1057823207929641658700761)
                    ·
                      rfl

theorem cell22_3090155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_3090155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090155 prefixEnd_3090155 := by exact prefixLift 3090155
  have htrace : WordTrace (prefixWord ++ tailWord_3090155) baseStart_3090155 baseEnd_3090155 := by
    simpa [prefixWord, tailWord_3090155, baseEnd_3090155] using wordTrace_append hprefix tailTrace_3090155
  have hstable : (prefixWord ++ tailWord_3090155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090155).length < 2 ^ (prefixWord ++ tailWord_3090155).sum := by decide
  have hdescent : baseEnd_3090155 < baseStart_3090155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090172 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_3090172 : Nat := 118140960795 + 3090172 * 2 ^ 59
def prefixEnd_3090172 : Nat := 4983230072969 + 3 ^ 40 * 3090172 * 2
def baseEnd_3090172 : Nat := 1057829027377059281025709

theorem tailTrace_3090172 : CollatzResearch.WordTrace tailWord_3090172 prefixEnd_3090172 1057829027377059281025709 := by
  unfold tailWord_3090172
  simp only [CollatzResearch.WordTrace]
  refine ⟨56353916080421039102820385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75138554773894718803760513 56353916080421039102820385)
  ·
    refine ⟨42265437060315779327115289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56353916080421039102820385 42265437060315779327115289)
    ·
      refine ⟨31699077795236834495336467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42265437060315779327115289 31699077795236834495336467)
      ·
        refine ⟨47548616692855251743004701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31699077795236834495336467 47548616692855251743004701)
        ·
          refine ⟨17830731259820719403626763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47548616692855251743004701 17830731259820719403626763)
          ·
            refine ⟨26746096889731079105440145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17830731259820719403626763 26746096889731079105440145)
            ·
              refine ⟨20059572667298309329080109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26746096889731079105440145 20059572667298309329080109)
              ·
                refine ⟨7522339750236865998405041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20059572667298309329080109 7522339750236865998405041)
                ·
                  refine ⟨5641754812677649498803781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7522339750236865998405041 5641754812677649498803781)
                  ·
                    refine ⟨1057829027377059281025709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641754812677649498803781 1057829027377059281025709)
                    ·
                      rfl

theorem cell22_3090172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_3090172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090172 prefixEnd_3090172 := by exact prefixLift 3090172
  have htrace : WordTrace (prefixWord ++ tailWord_3090172) baseStart_3090172 baseEnd_3090172 := by
    simpa [prefixWord, tailWord_3090172, baseEnd_3090172] using wordTrace_append hprefix tailTrace_3090172
  have hstable : (prefixWord ++ tailWord_3090172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090172).length < 2 ^ (prefixWord ++ tailWord_3090172).sum := by decide
  have hdescent : baseEnd_3090172 < baseStart_3090172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090279 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3090279 : Nat := 118140960795 + 3090279 * 2 ^ 59
def prefixEnd_3090279 : Nat := 4983230072969 + 3 ^ 40 * 3090279 * 2
def baseEnd_3090279 : Nat := 1057865655663746668600381

theorem tailTrace_3090279 : CollatzResearch.WordTrace tailWord_3090279 prefixEnd_3090279 1057865655663746668600381 := by
  unfold tailWord_3090279
  simp only [CollatzResearch.WordTrace]
  refine ⟨112711734771454435479785891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75141156514302956986523927 112711734771454435479785891)
  ·
    refine ⟨169067602157181653219678837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112711734771454435479785891 169067602157181653219678837)
    ·
      refine ⟨15850087702235779989344891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169067602157181653219678837 15850087702235779989344891)
      ·
        refine ⟨23775131553353669984017337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15850087702235779989344891 23775131553353669984017337)
        ·
          refine ⟨17831348665015252488013003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23775131553353669984017337 17831348665015252488013003)
          ·
            refine ⟨26747022997522878732019505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17831348665015252488013003 26747022997522878732019505)
            ·
              refine ⟨20060267248142159049014629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26747022997522878732019505 20060267248142159049014629)
              ·
                refine ⟨3761300109026654821690243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20060267248142159049014629 3761300109026654821690243)
                ·
                  refine ⟨5641950163539982232535365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761300109026654821690243 5641950163539982232535365)
                  ·
                    refine ⟨1057865655663746668600381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5641950163539982232535365 1057865655663746668600381)
                    ·
                      rfl

theorem cell22_3090279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3090279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090279 prefixEnd_3090279 := by exact prefixLift 3090279
  have htrace : WordTrace (prefixWord ++ tailWord_3090279) baseStart_3090279 baseEnd_3090279 := by
    simpa [prefixWord, tailWord_3090279, baseEnd_3090279] using wordTrace_append hprefix tailTrace_3090279
  have hstable : (prefixWord ++ tailWord_3090279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090279).length < 2 ^ (prefixWord ++ tailWord_3090279).sum := by decide
  have hdescent : baseEnd_3090279 < baseStart_3090279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090309 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 4, 3]
def baseStart_3090309 : Nat := 118140960795 + 3090309 * 2 ^ 59
def prefixEnd_3090309 : Nat := 4983230072969 + 3 ^ 40 * 3090309 * 2
def baseEnd_3090309 : Nat := 1057875925276836590350289

theorem tailTrace_3090309 : CollatzResearch.WordTrace tailWord_3090309 prefixEnd_3090309 1057875925276836590350289 := by
  unfold tailWord_3090309
  simp only [CollatzResearch.WordTrace]
  refine ⟨112712828961345750603377981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75141885974230500402251987 112712828961345750603377981)
  ·
    refine ⟨42267310860504656476266743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112712828961345750603377981 42267310860504656476266743)
    ·
      refine ⟨63400966290756984714400115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42267310860504656476266743 63400966290756984714400115)
      ·
        refine ⟨95101449436135477071600173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63400966290756984714400115 95101449436135477071600173)
        ·
          refine ⟨35663043538550803901850065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95101449436135477071600173 35663043538550803901850065)
          ·
            refine ⟨26747282653913102926387549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35663043538550803901850065 26747282653913102926387549)
            ·
              refine ⟨10030230995217413597395331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26747282653913102926387549 10030230995217413597395331)
              ·
                refine ⟨15045346492826120396092997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10030230995217413597395331 15045346492826120396092997)
                ·
                  refine ⟨2821002467404897574267437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15045346492826120396092997 2821002467404897574267437)
                  ·
                    refine ⟨1057875925276836590350289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821002467404897574267437 1057875925276836590350289)
                    ·
                      rfl

theorem cell22_3090309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 3].length) (baseStart_3090309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090309 prefixEnd_3090309 := by exact prefixLift 3090309
  have htrace : WordTrace (prefixWord ++ tailWord_3090309) baseStart_3090309 baseEnd_3090309 := by
    simpa [prefixWord, tailWord_3090309, baseEnd_3090309] using wordTrace_append hprefix tailTrace_3090309
  have hstable : (prefixWord ++ tailWord_3090309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090309).length < 2 ^ (prefixWord ++ tailWord_3090309).sum := by decide
  have hdescent : baseEnd_3090309 < baseStart_3090309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090324 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_3090324 : Nat := 118140960795 + 3090324 * 2 ^ 59
def prefixEnd_3090324 : Nat := 4983230072969 + 3 ^ 40 * 3090324 * 2
def baseEnd_3090324 : Nat := 1057881060083381551225243

theorem tailTrace_3090324 : CollatzResearch.WordTrace tailWord_3090324 prefixEnd_3090324 1057881060083381551225243 := by
  unfold tailWord_3090324
  simp only [CollatzResearch.WordTrace]
  refine ⟨56356688028145704082587013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75142250704194272110116017 56356688028145704082587013)
  ·
    refine ⟨10566879005277319515485065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56356688028145704082587013 10566879005277319515485065)
    ·
      refine ⟨7925159253957989636613799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10566879005277319515485065 7925159253957989636613799)
      ·
        refine ⟨11887738880936984454920699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925159253957989636613799 11887738880936984454920699)
        ·
          refine ⟨17831608321405476682381049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11887738880936984454920699 17831608321405476682381049)
          ·
            refine ⟨13373706241054107511785787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17831608321405476682381049 13373706241054107511785787)
            ·
              refine ⟨20060559361581161267678681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13373706241054107511785787 20060559361581161267678681)
              ·
                refine ⟨15045419521185870950759011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20060559361581161267678681 15045419521185870950759011)
                ·
                  refine ⟨22568129281778806426138517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15045419521185870950759011 22568129281778806426138517)
                  ·
                    refine ⟨1057881060083381551225243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22568129281778806426138517 1057881060083381551225243)
                    ·
                      rfl

theorem cell22_3090324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_3090324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090324 prefixEnd_3090324 := by exact prefixLift 3090324
  have htrace : WordTrace (prefixWord ++ tailWord_3090324) baseStart_3090324 baseEnd_3090324 := by
    simpa [prefixWord, tailWord_3090324, baseEnd_3090324] using wordTrace_append hprefix tailTrace_3090324
  have hstable : (prefixWord ++ tailWord_3090324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090324).length < 2 ^ (prefixWord ++ tailWord_3090324).sum := by decide
  have hdescent : baseEnd_3090324 < baseStart_3090324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090354 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_3090354 : Nat := 118140960795 + 3090354 * 2 ^ 59
def prefixEnd_3090354 : Nat := 4983230072969 + 3 ^ 40 * 3090354 * 2
def baseEnd_3090354 : Nat := 1057891329696471472975151

theorem tailTrace_3090354 : CollatzResearch.WordTrace tailWord_3090354 prefixEnd_3090354 1057891329696471472975151 := by
  unfold tailWord_3090354
  simp only [CollatzResearch.WordTrace]
  refine ⟨28178617561545680822191529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75142980164121815525844077 28178617561545680822191529)
  ·
    refine ⟨21133963171159260616643647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28178617561545680822191529 21133963171159260616643647)
    ·
      refine ⟨31700944756738890924965471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21133963171159260616643647 31700944756738890924965471)
      ·
        refine ⟨47551417135108336387448207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31700944756738890924965471 47551417135108336387448207)
        ·
          refine ⟨71327125702662504581172311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47551417135108336387448207 71327125702662504581172311)
          ·
            refine ⟨106990688553993756871758467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71327125702662504581172311 106990688553993756871758467)
            ·
              refine ⟨160486032830990635307637701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106990688553993756871758467 160486032830990635307637701)
              ·
                refine ⟨30091131155810744120182069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160486032830990635307637701 30091131155810744120182069)
                ·
                  refine ⟨2821043545857257261267069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30091131155810744120182069 2821043545857257261267069)
                  ·
                    refine ⟨1057891329696471472975151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821043545857257261267069 1057891329696471472975151)
                    ·
                      rfl

theorem cell22_3090354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_3090354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090354 prefixEnd_3090354 := by exact prefixLift 3090354
  have htrace : WordTrace (prefixWord ++ tailWord_3090354) baseStart_3090354 baseEnd_3090354 := by
    simpa [prefixWord, tailWord_3090354, baseEnd_3090354] using wordTrace_append hprefix tailTrace_3090354
  have hstable : (prefixWord ++ tailWord_3090354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090354).length < 2 ^ (prefixWord ++ tailWord_3090354).sum := by decide
  have hdescent : baseEnd_3090354 < baseStart_3090354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090367 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 7]
def baseStart_3090367 : Nat := 118140960795 + 3090367 * 2 ^ 59
def prefixEnd_3090367 : Nat := 4983230072969 + 3 ^ 40 * 3090367 * 2
def baseEnd_3090367 : Nat := 352631926620714590800037

theorem tailTrace_3090367 : CollatzResearch.WordTrace tailWord_3090367 prefixEnd_3090367 352631926620714590800037 := by
  unfold tailWord_3090367
  simp only [CollatzResearch.WordTrace]
  refine ⟨112714944395135626508989355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75143296263423751005992903 112714944395135626508989355)
  ·
    refine ⟨169072416592703439763484033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112714944395135626508989355 169072416592703439763484033)
    ·
      refine ⟨126804312444527579822613025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169072416592703439763484033 126804312444527579822613025)
      ·
        refine ⟨95103234333395684866959769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126804312444527579822613025 95103234333395684866959769)
        ·
          refine ⟨71327425750046763650219827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95103234333395684866959769 71327425750046763650219827)
          ·
            refine ⟨106991138625070145475329741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71327425750046763650219827 106991138625070145475329741)
            ·
              refine ⟨40121676984401304553248653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106991138625070145475329741 40121676984401304553248653)
              ·
                refine ⟨15045628869150489207468245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40121676984401304553248653 15045628869150489207468245)
                ·
                  refine ⟨352631926620714590800037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15045628869150489207468245 352631926620714590800037)
                  ·
                    rfl

theorem cell22_3090367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 7].length) (baseStart_3090367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090367 prefixEnd_3090367 := by exact prefixLift 3090367
  have htrace : WordTrace (prefixWord ++ tailWord_3090367) baseStart_3090367 baseEnd_3090367 := by
    simpa [prefixWord, tailWord_3090367, baseEnd_3090367] using wordTrace_append hprefix tailTrace_3090367
  have hstable : (prefixWord ++ tailWord_3090367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090367).length < 2 ^ (prefixWord ++ tailWord_3090367).sum := by decide
  have hdescent : baseEnd_3090367 < baseStart_3090367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090459 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 2, 4]
def baseStart_3090459 : Nat := 118140960795 + 3090459 * 2 ^ 59
def prefixEnd_3090459 : Nat := 4983230072969 + 3 ^ 40 * 3090459 * 2
def baseEnd_3090459 : Nat := 1057927273342286199099829

theorem tailTrace_3090459 : CollatzResearch.WordTrace tailWord_3090459 prefixEnd_3090459 1057927273342286199099829 := by
  unfold tailWord_3090459
  simp only [CollatzResearch.WordTrace]
  refine ⟨112718299910802326221338431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75145533273868217480892287 112718299910802326221338431)
  ·
    refine ⟨169077449866203489332007647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112718299910802326221338431 169077449866203489332007647)
    ·
      refine ⟨253616174799305233998011471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169077449866203489332007647 253616174799305233998011471)
      ·
        refine ⟨380424262198957850997017207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253616174799305233998011471 380424262198957850997017207)
        ·
          refine ⟨570636393298436776495525811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380424262198957850997017207 570636393298436776495525811)
          ·
            refine ⟨855954589947655164743288717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570636393298436776495525811 855954589947655164743288717)
            ·
              refine ⟨320982971230370686778733269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855954589947655164743288717 320982971230370686778733269)
              ·
                refine ⟨7523038388211812971376561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 320982971230370686778733269 7523038388211812971376561)
                ·
                  refine ⟨5642278791158859728532421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7523038388211812971376561 5642278791158859728532421)
                  ·
                    refine ⟨1057927273342286199099829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642278791158859728532421 1057927273342286199099829)
                    ·
                      rfl

theorem cell22_3090459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 4].length) (baseStart_3090459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090459 prefixEnd_3090459 := by exact prefixLift 3090459
  have htrace : WordTrace (prefixWord ++ tailWord_3090459) baseStart_3090459 baseEnd_3090459 := by
    simpa [prefixWord, tailWord_3090459, baseEnd_3090459] using wordTrace_append hprefix tailTrace_3090459
  have hstable : (prefixWord ++ tailWord_3090459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090459).length < 2 ^ (prefixWord ++ tailWord_3090459).sum := by decide
  have hdescent : baseEnd_3090459 < baseStart_3090459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090461 : List Nat := [1, 4, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3090461 : Nat := 118140960795 + 3090461 * 2 ^ 59
def prefixEnd_3090461 : Nat := 4983230072969 + 3 ^ 40 * 3090461 * 2
def baseEnd_3090461 : Nat := 1057927957983158860549823

theorem tailTrace_3090461 : CollatzResearch.WordTrace tailWord_3090461 prefixEnd_3090461 1057927957983158860549823 := by
  unfold tailWord_3090461
  simp only [CollatzResearch.WordTrace]
  refine ⟨112718372856795080562911237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75145581904530053708607491 112718372856795080562911237)
  ·
    refine ⟨21134694910649077605545857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112718372856795080562911237 21134694910649077605545857)
    ·
      refine ⟨15851021182986808204159393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21134694910649077605545857 15851021182986808204159393)
      ·
        refine ⟨11888265887240106153119545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15851021182986808204159393 11888265887240106153119545)
        ·
          refine ⟨8916199415430079614839659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11888265887240106153119545 8916199415430079614839659)
          ·
            refine ⟨13374299123145119422259489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916199415430079614839659 13374299123145119422259489)
            ·
              refine ⟨10030724342358839566694617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13374299123145119422259489 10030724342358839566694617)
              ·
                refine ⟨7523043256769129675020963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10030724342358839566694617 7523043256769129675020963)
                ·
                  refine ⟨11284564885153694512531445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523043256769129675020963 11284564885153694512531445)
                  ·
                    refine ⟨1057927957983158860549823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11284564885153694512531445 1057927957983158860549823)
                    ·
                      rfl

theorem cell22_3090461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3090461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090461 prefixEnd_3090461 := by exact prefixLift 3090461
  have htrace : WordTrace (prefixWord ++ tailWord_3090461) baseStart_3090461 baseEnd_3090461 := by
    simpa [prefixWord, tailWord_3090461, baseEnd_3090461] using wordTrace_append hprefix tailTrace_3090461
  have hstable : (prefixWord ++ tailWord_3090461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090461).length < 2 ^ (prefixWord ++ tailWord_3090461).sum := by decide
  have hdescent : baseEnd_3090461 < baseStart_3090461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090465 : List Nat := [1, 2, 3, 2, 4, 2, 2, 1, 1, 4]
def baseStart_3090465 : Nat := 118140960795 + 3090465 * 2 ^ 59
def prefixEnd_3090465 : Nat := 4983230072969 + 3 ^ 40 * 3090465 * 2
def baseEnd_3090465 : Nat := 1057929327264904183449811

theorem tailTrace_3090465 : CollatzResearch.WordTrace tailWord_3090465 prefixEnd_3090465 1057929327264904183449811 := by
  unfold tailWord_3090465
  simp only [CollatzResearch.WordTrace]
  refine ⟨112718518748780589246056849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75145679165853726164037899 112718518748780589246056849)
  ·
    refine ⟨84538889061585441934542637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112718518748780589246056849 84538889061585441934542637)
    ·
      refine ⟨31702083398094540725453489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84538889061585441934542637 31702083398094540725453489)
      ·
        refine ⟨23776562548570905544090117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31702083398094540725453489 23776562548570905544090117)
        ·
          refine ⟨4458105477857044789516897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23776562548570905544090117 4458105477857044789516897)
          ·
            refine ⟨3343579108392783592137673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4458105477857044789516897 3343579108392783592137673)
            ·
              refine ⟨2507684331294587694103255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3343579108392783592137673 2507684331294587694103255)
              ·
                refine ⟨3761526496941881541154883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507684331294587694103255 3761526496941881541154883)
                ·
                  refine ⟨5642289745412822311732325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3761526496941881541154883 5642289745412822311732325)
                  ·
                    refine ⟨1057929327264904183449811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5642289745412822311732325 1057929327264904183449811)
                    ·
                      rfl

theorem cell22_3090465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_3090465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090465 prefixEnd_3090465 := by exact prefixLift 3090465
  have htrace : WordTrace (prefixWord ++ tailWord_3090465) baseStart_3090465 baseEnd_3090465 := by
    simpa [prefixWord, tailWord_3090465, baseEnd_3090465] using wordTrace_append hprefix tailTrace_3090465
  have hstable : (prefixWord ++ tailWord_3090465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090465).length < 2 ^ (prefixWord ++ tailWord_3090465).sum := by decide
  have hdescent : baseEnd_3090465 < baseStart_3090465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090478 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3090478 : Nat := 118140960795 + 3090478 * 2 ^ 59
def prefixEnd_3090478 : Nat := 4983230072969 + 3 ^ 40 * 3090478 * 2
def baseEnd_3090478 : Nat := 1057933777430576482874771

theorem tailTrace_3090478 : CollatzResearch.WordTrace tailWord_3090478 prefixEnd_3090478 1057933777430576482874771 := by
  unfold tailWord_3090478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14089874112216686558285011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75145995265155661644186725 14089874112216686558285011)
  ·
    refine ⟨21134811168325029837427517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14089874112216686558285011 21134811168325029837427517)
    ·
      refine ⟨7925554188121886189035319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21134811168325029837427517 7925554188121886189035319)
      ·
        refine ⟨11888331282182829283552979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925554188121886189035319 11888331282182829283552979)
        ·
          refine ⟨17832496923274243925329469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11888331282182829283552979 17832496923274243925329469)
          ·
            refine ⟨6687186346227841471998551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17832496923274243925329469 6687186346227841471998551)
            ·
              refine ⟨10030779519341762207997827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687186346227841471998551 10030779519341762207997827)
              ·
                refine ⟨15046169279012643311996741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10030779519341762207997827 15046169279012643311996741)
                ·
                  refine ⟨2821156739814870620999389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15046169279012643311996741 2821156739814870620999389)
                  ·
                    refine ⟨1057933777430576482874771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821156739814870620999389 1057933777430576482874771)
                    ·
                      rfl

theorem cell22_3090478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3090478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090478 prefixEnd_3090478 := by exact prefixLift 3090478
  have htrace : WordTrace (prefixWord ++ tailWord_3090478) baseStart_3090478 baseEnd_3090478 := by
    simpa [prefixWord, tailWord_3090478, baseEnd_3090478] using wordTrace_append hprefix tailTrace_3090478
  have hstable : (prefixWord ++ tailWord_3090478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090478).length < 2 ^ (prefixWord ++ tailWord_3090478).sum := by decide
  have hdescent : baseEnd_3090478 < baseStart_3090478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090519 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 7]
def baseStart_3090519 : Nat := 118140960795 + 3090519 * 2 ^ 59
def prefixEnd_3090519 : Nat := 4983230072969 + 3 ^ 40 * 3090519 * 2
def baseEnd_3090519 : Nat := 352649270856155347533215

theorem tailTrace_3090519 : CollatzResearch.WordTrace tailWord_3090519 prefixEnd_3090519 352649270856155347533215 := by
  unfold tailWord_3090519
  simp only [CollatzResearch.WordTrace]
  refine ⟨112720488290584956468522611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75146992193723304312348407 112720488290584956468522611)
  ·
    refine ⟨169080732435877434702783917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112720488290584956468522611 169080732435877434702783917)
    ·
      refine ⟨63405274663454038013543969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169080732435877434702783917 63405274663454038013543969)
      ·
        refine ⟨47553955997590528510157977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63405274663454038013543969 47553955997590528510157977)
        ·
          refine ⟨35665466998192896382618483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47553955997590528510157977 35665466998192896382618483)
          ·
            refine ⟨53498200497289344573927725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35665466998192896382618483 53498200497289344573927725)
            ·
              refine ⟨20061825186483504215222897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53498200497289344573927725 20061825186483504215222897)
              ·
                refine ⟨15046368889862628161417173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20061825186483504215222897 15046368889862628161417173)
                ·
                  refine ⟨352649270856155347533215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15046368889862628161417173 352649270856155347533215)
                  ·
                    rfl

theorem cell22_3090519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 7].length) (baseStart_3090519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090519 prefixEnd_3090519 := by exact prefixLift 3090519
  have htrace : WordTrace (prefixWord ++ tailWord_3090519) baseStart_3090519 baseEnd_3090519 := by
    simpa [prefixWord, tailWord_3090519, baseEnd_3090519] using wordTrace_append hprefix tailTrace_3090519
  have hstable : (prefixWord ++ tailWord_3090519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090519).length < 2 ^ (prefixWord ++ tailWord_3090519).sum := by decide
  have hdescent : baseEnd_3090519 < baseStart_3090519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090553 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 5]
def baseStart_3090553 : Nat := 118140960795 + 3090553 * 2 ^ 59
def prefixEnd_3090553 : Nat := 4983230072969 + 3 ^ 40 * 3090553 * 2
def baseEnd_3090553 : Nat := 352653150487767095749847

theorem tailTrace_3090553 : CollatzResearch.WordTrace tailWord_3090553 prefixEnd_3090553 352653150487767095749847 := by
  unfold tailWord_3090553
  simp only [CollatzResearch.WordTrace]
  refine ⟨112721728372461780275260313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75147818914974520183506875 112721728372461780275260313)
  ·
    refine ⟨84541296279346335206445235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112721728372461780275260313 84541296279346335206445235)
    ·
      refine ⟨126811944419019502809667853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84541296279346335206445235 126811944419019502809667853)
      ·
        refine ⟨47554479157132313553625445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126811944419019502809667853 47554479157132313553625445)
        ·
          refine ⟨8916464841962308791304771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47554479157132313553625445 8916464841962308791304771)
          ·
            refine ⟨13374697262943463186957157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8916464841962308791304771 13374697262943463186957157)
            ·
              refine ⟨2507755736801899347554467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13374697262943463186957157 2507755736801899347554467)
              ·
                refine ⟨3761633605202849021331701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507755736801899347554467 3761633605202849021331701)
                ·
                  refine ⟨352653150487767095749847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3761633605202849021331701 352653150487767095749847)
                  ·
                    rfl

theorem cell22_3090553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_3090553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090553 prefixEnd_3090553 := by exact prefixLift 3090553
  have htrace : WordTrace (prefixWord ++ tailWord_3090553) baseStart_3090553 baseEnd_3090553 := by
    simpa [prefixWord, tailWord_3090553, baseEnd_3090553] using wordTrace_append hprefix tailTrace_3090553
  have hstable : (prefixWord ++ tailWord_3090553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090553).length < 2 ^ (prefixWord ++ tailWord_3090553).sum := by decide
  have hdescent : baseEnd_3090553 < baseStart_3090553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090628 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_3090628 : Nat := 118140960795 + 3090628 * 2 ^ 59
def prefixEnd_3090628 : Nat := 4983230072969 + 3 ^ 40 * 3090628 * 2
def baseEnd_3090628 : Nat := 1057985125496026091624311

theorem tailTrace_3090628 : CollatzResearch.WordTrace tailWord_3090628 prefixEnd_3090628 1057985125496026091624311 := by
  unfold tailWord_3090628
  simp only [CollatzResearch.WordTrace]
  refine ⟨56362231923595034042120269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75149642564793378722827025 56362231923595034042120269)
  ·
    refine ⟨21135836971348137765795101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56362231923595034042120269 21135836971348137765795101)
    ·
      refine ⟨7925938864255551662173163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21135836971348137765795101 7925938864255551662173163)
      ·
        refine ⟨11888908296383327493259745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7925938864255551662173163 11888908296383327493259745)
        ·
          refine ⟨8916681222287495619944809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11888908296383327493259745 8916681222287495619944809)
          ·
            refine ⟨6687510916715621714958607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8916681222287495619944809 6687510916715621714958607)
            ·
              refine ⟨10031266375073432572437911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6687510916715621714958607 10031266375073432572437911)
              ·
                refine ⟨15046899562610148858656867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10031266375073432572437911 15046899562610148858656867)
                ·
                  refine ⟨22570349343915223287985301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15046899562610148858656867 22570349343915223287985301)
                  ·
                    refine ⟨1057985125496026091624311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22570349343915223287985301 1057985125496026091624311)
                    ·
                      rfl

theorem cell22_3090628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_3090628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090628 prefixEnd_3090628 := by exact prefixLift 3090628
  have htrace : WordTrace (prefixWord ++ tailWord_3090628) baseStart_3090628 baseEnd_3090628 := by
    simpa [prefixWord, tailWord_3090628, baseEnd_3090628] using wordTrace_append hprefix tailTrace_3090628
  have hstable : (prefixWord ++ tailWord_3090628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090628).length < 2 ^ (prefixWord ++ tailWord_3090628).sum := by decide
  have hdescent : baseEnd_3090628 < baseStart_3090628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090722 : List Nat := [3, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_3090722 : Nat := 118140960795 + 3090722 * 2 ^ 59
def prefixEnd_3090722 : Nat := 4983230072969 + 3 ^ 40 * 3090722 * 2
def baseEnd_3090722 : Nat := 352672434539013726591341

theorem tailTrace_3090722 : CollatzResearch.WordTrace tailWord_3090722 prefixEnd_3090722 352672434539013726591341 := by
  unfold tailWord_3090722
  simp only [CollatzResearch.WordTrace]
  refine ⟨28181973077212380534540605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75151928205899681425441613 28181973077212380534540605)
  ·
    refine ⟨10568239903954642700452727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28181973077212380534540605 10568239903954642700452727)
    ·
      refine ⟨15852359855931964050679091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10568239903954642700452727 15852359855931964050679091)
      ·
        refine ⟨23778539783897946076018637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15852359855931964050679091 23778539783897946076018637)
        ·
          refine ⟨8916952418961729778506989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23778539783897946076018637 8916952418961729778506989)
          ·
            refine ⟨3343857157110648666940121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8916952418961729778506989 3343857157110648666940121)
            ·
              refine ⟨2507892867832986500205091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3343857157110648666940121 2507892867832986500205091)
              ·
                refine ⟨3761839301749479750307637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2507892867832986500205091 3761839301749479750307637)
                ·
                  refine ⟨352672434539013726591341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3761839301749479750307637 352672434539013726591341)
                  ·
                    rfl

theorem cell22_3090722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_3090722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090722 prefixEnd_3090722 := by exact prefixLift 3090722
  have htrace : WordTrace (prefixWord ++ tailWord_3090722) baseStart_3090722 baseEnd_3090722 := by
    simpa [prefixWord, tailWord_3090722, baseEnd_3090722] using wordTrace_append hprefix tailTrace_3090722
  have hstable : (prefixWord ++ tailWord_3090722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090722).length < 2 ^ (prefixWord ++ tailWord_3090722).sum := by decide
  have hdescent : baseEnd_3090722 < baseStart_3090722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090748 : List Nat := [2, 2, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_3090748 : Nat := 118140960795 + 3090748 * 2 ^ 59
def prefixEnd_3090748 : Nat := 4983230072969 + 3 ^ 40 * 3090748 * 2
def baseEnd_3090748 : Nat := 1058026203948385778623943

theorem tailTrace_3090748 : CollatzResearch.WordTrace tailWord_3090748 prefixEnd_3090748 1058026203948385778623943 := by
  unfold tailWord_3090748
  simp only [CollatzResearch.WordTrace]
  refine ⟨56364420303377664289304449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75152560404503552385739265 56364420303377664289304449)
  ·
    refine ⟨42273315227533248216978337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56364420303377664289304449 42273315227533248216978337)
    ·
      refine ⟨31704986420649936162733753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42273315227533248216978337 31704986420649936162733753)
      ·
        refine ⟨23778739815487452122050315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31704986420649936162733753 23778739815487452122050315)
        ·
          refine ⟨35668109723231178183075473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23778739815487452122050315 35668109723231178183075473)
          ·
            refine ⟨26751082292423383637306605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35668109723231178183075473 26751082292423383637306605)
            ·
              refine ⟨10031655859658768863989977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26751082292423383637306605 10031655859658768863989977)
              ·
                refine ⟨7523741894744076647992483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10031655859658768863989977 7523741894744076647992483)
                ·
                  refine ⟨11285612842116114971988725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7523741894744076647992483 11285612842116114971988725)
                  ·
                    refine ⟨1058026203948385778623943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11285612842116114971988725 1058026203948385778623943)
                    ·
                      rfl

theorem cell22_3090748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_3090748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090748 prefixEnd_3090748 := by exact prefixLift 3090748
  have htrace : WordTrace (prefixWord ++ tailWord_3090748) baseStart_3090748 baseEnd_3090748 := by
    simpa [prefixWord, tailWord_3090748, baseEnd_3090748] using wordTrace_append hprefix tailTrace_3090748
  have hstable : (prefixWord ++ tailWord_3090748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090748).length < 2 ^ (prefixWord ++ tailWord_3090748).sum := by decide
  have hdescent : baseEnd_3090748 < baseStart_3090748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090823 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 7]
def baseStart_3090823 : Nat := 118140960795 + 3090823 * 2 ^ 59
def prefixEnd_3090823 : Nat := 4983230072969 + 3 ^ 40 * 3090823 * 2
def baseEnd_3090823 : Nat := 352683959327036860999571

theorem tailTrace_3090823 : CollatzResearch.WordTrace tailWord_3090823 prefixEnd_3090823 352683959327036860999571 := by
  unfold tailWord_3090823
  simp only [CollatzResearch.WordTrace]
  refine ⟨112731576081483616387589123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75154384054322410925059415 112731576081483616387589123)
  ·
    refine ⟨169097364122225424581383685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112731576081483616387589123 169097364122225424581383685)
    ·
      refine ⟨31705755772917267109009441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169097364122225424581383685 31705755772917267109009441)
      ·
        refine ⟨23779316829687950331757081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31705755772917267109009441 23779316829687950331757081)
        ·
          refine ⟨17834487622265962748817811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23779316829687950331757081 17834487622265962748817811)
          ·
            refine ⟨26751731433398944123226717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17834487622265962748817811 26751731433398944123226717)
            ·
              refine ⟨10031899287524604046210019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26751731433398944123226717 10031899287524604046210019)
              ·
                refine ⟨15047848931286906069315029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10031899287524604046210019 15047848931286906069315029)
                ·
                  refine ⟨352683959327036860999571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15047848931286906069315029 352683959327036860999571)
                  ·
                    rfl

theorem cell22_3090823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 7].length) (baseStart_3090823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090823 prefixEnd_3090823 := by exact prefixLift 3090823
  have htrace : WordTrace (prefixWord ++ tailWord_3090823) baseStart_3090823 baseEnd_3090823 := by
    simpa [prefixWord, tailWord_3090823, baseEnd_3090823] using wordTrace_append hprefix tailTrace_3090823
  have hstable : (prefixWord ++ tailWord_3090823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090823).length < 2 ^ (prefixWord ++ tailWord_3090823).sum := by decide
  have hdescent : baseEnd_3090823 < baseStart_3090823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090827 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 1, 3]
def baseStart_3090827 : Nat := 118140960795 + 3090827 * 2 ^ 59
def prefixEnd_3090827 : Nat := 4983230072969 + 3 ^ 40 * 3090827 * 2
def baseEnd_3090827 : Nat := 1058053247262855905898701

theorem tailTrace_3090827 : CollatzResearch.WordTrace tailWord_3090827 prefixEnd_3090827 1058053247262855905898701 := by
  unfold tailWord_3090827
  simp only [CollatzResearch.WordTrace]
  refine ⟨112731721973469125070734735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75154481315646083380489823 112731721973469125070734735)
  ·
    refine ⟨169097582960203687606102103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112731721973469125070734735 169097582960203687606102103)
    ·
      refine ⟨253646374440305531409153155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169097582960203687606102103 253646374440305531409153155)
      ·
        refine ⟨380469561660458297113729733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253646374440305531409153155 380469561660458297113729733)
        ·
          refine ⟨71338042811335930708824325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 380469561660458297113729733 71338042811335930708824325)
          ·
            refine ⟨13375883027125487007904561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71338042811335930708824325 13375883027125487007904561)
            ·
              refine ⟨10031912270344115255928421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13375883027125487007904561 10031912270344115255928421)
              ·
                refine ⟨1880983550689521610486579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10031912270344115255928421 1880983550689521610486579)
                ·
                  refine ⟨2821475326034282415729869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1880983550689521610486579 2821475326034282415729869)
                  ·
                    refine ⟨1058053247262855905898701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821475326034282415729869 1058053247262855905898701)
                    ·
                      rfl

theorem cell22_3090827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 3].length) (baseStart_3090827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090827 prefixEnd_3090827 := by exact prefixLift 3090827
  have htrace : WordTrace (prefixWord ++ tailWord_3090827) baseStart_3090827 baseEnd_3090827 := by
    simpa [prefixWord, tailWord_3090827, baseEnd_3090827] using wordTrace_append hprefix tailTrace_3090827
  have hstable : (prefixWord ++ tailWord_3090827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090827).length < 2 ^ (prefixWord ++ tailWord_3090827).sum := by decide
  have hdescent : baseEnd_3090827 < baseStart_3090827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090913 : List Nat := [1, 2, 3, 1, 2, 2, 1, 10]
def baseStart_3090913 : Nat := 118140960795 + 3090913 * 2 ^ 59
def prefixEnd_3090913 : Nat := 4983230072969 + 3 ^ 40 * 3090913 * 2
def baseEnd_3090913 : Nat := 117564742980042260916493

theorem tailTrace_3090913 : CollatzResearch.WordTrace tailWord_3090913 prefixEnd_3090913 117564742980042260916493 := by
  unfold tailWord_3090913
  simp only [CollatzResearch.WordTrace]
  refine ⟨112734858651157561758365393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75156572434105041172243595 112734858651157561758365393)
  ·
    refine ⟨84551143988368171318774045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112734858651157561758365393 84551143988368171318774045)
    ·
      refine ⟨31706678995638064244540267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84551143988368171318774045 31706678995638064244540267)
      ·
        refine ⟨47560018493457096366810401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31706678995638064244540267 47560018493457096366810401)
        ·
          refine ⟨35670013870092822275107801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47560018493457096366810401 35670013870092822275107801)
          ·
            refine ⟨26752510402569616706330851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35670013870092822275107801 26752510402569616706330851)
            ·
              refine ⟨40128765603854425059496277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26752510402569616706330851 40128765603854425059496277)
              ·
                refine ⟨117564742980042260916493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40128765603854425059496277 117564742980042260916493)
                ·
                  rfl

theorem cell22_3090913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 10].length) (baseStart_3090913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090913 prefixEnd_3090913 := by exact prefixLift 3090913
  have htrace : WordTrace (prefixWord ++ tailWord_3090913) baseStart_3090913 baseEnd_3090913 := by
    simpa [prefixWord, tailWord_3090913, baseEnd_3090913] using wordTrace_append hprefix tailTrace_3090913
  have hstable : (prefixWord ++ tailWord_3090913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090913).length < 2 ^ (prefixWord ++ tailWord_3090913).sum := by decide
  have hdescent : baseEnd_3090913 < baseStart_3090913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090917 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_3090917 : Nat := 118140960795 + 3090917 * 2 ^ 59
def prefixEnd_3090917 : Nat := 4983230072969 + 3 ^ 40 * 3090917 * 2
def baseEnd_3090917 : Nat := 1058084056102125671148425

theorem tailTrace_3090917 : CollatzResearch.WordTrace tailWord_3090917 prefixEnd_3090917 1058084056102125671148425 := by
  unfold tailWord_3090917
  simp only [CollatzResearch.WordTrace]
  refine ⟨112735004543143070441511005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75156669695428713627674003 112735004543143070441511005)
  ·
    refine ⟨42275626703678651415566627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112735004543143070441511005 42275626703678651415566627)
    ·
      refine ⟨63413440055517977123349941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42275626703678651415566627 63413440055517977123349941)
      ·
        refine ⟨5945010005204810355314057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63413440055517977123349941 5945010005204810355314057)
        ·
          refine ⟨4458757503903607766485543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5945010005204810355314057 4458757503903607766485543)
          ·
            refine ⟨6688136255855411649728315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4458757503903607766485543 6688136255855411649728315)
            ·
              refine ⟨10032204383783117474592473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6688136255855411649728315 10032204383783117474592473)
              ·
                refine ⟨7524153287837338105944355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10032204383783117474592473 7524153287837338105944355)
                ·
                  refine ⟨11286229931756007158916533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7524153287837338105944355 11286229931756007158916533)
                  ·
                    refine ⟨1058084056102125671148425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11286229931756007158916533 1058084056102125671148425)
                    ·
                      rfl

theorem cell22_3090917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_3090917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090917 prefixEnd_3090917 := by exact prefixLift 3090917
  have htrace : WordTrace (prefixWord ++ tailWord_3090917) baseStart_3090917 baseEnd_3090917 := by
    simpa [prefixWord, tailWord_3090917, baseEnd_3090917] using wordTrace_append hprefix tailTrace_3090917
  have hstable : (prefixWord ++ tailWord_3090917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090917).length < 2 ^ (prefixWord ++ tailWord_3090917).sum := by decide
  have hdescent : baseEnd_3090917 < baseStart_3090917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090930 : List Nat := [3, 2, 1, 4, 2, 10]
def baseStart_3090930 : Nat := 118140960795 + 3090930 * 2 ^ 59
def prefixEnd_3090930 : Nat := 4983230072969 + 3 ^ 40 * 3090930 * 2
def baseEnd_3090930 : Nat := 13062821065034542846585

theorem tailTrace_3090930 : CollatzResearch.WordTrace tailWord_3090930 prefixEnd_3090930 13062821065034542846585 := by
  unfold tailWord_3090930
  simp only [CollatzResearch.WordTrace]
  refine ⟨28183869673023993415433561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75156985794730649107822829 28183869673023993415433561)
  ·
    refine ⟨21137902254767995061575171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28183869673023993415433561 21137902254767995061575171)
    ·
      refine ⟨31706853382151992592362757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21137902254767995061575171 31706853382151992592362757)
      ·
        refine ⟨5945035009153498611068017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31706853382151992592362757 5945035009153498611068017)
        ·
          refine ⟨4458776256865123958301013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5945035009153498611068017 4458776256865123958301013)
          ·
            refine ⟨13062821065034542846585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4458776256865123958301013 13062821065034542846585)
            ·
              rfl

theorem cell22_3090930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 10].length) (baseStart_3090930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090930 prefixEnd_3090930 := by exact prefixLift 3090930
  have htrace : WordTrace (prefixWord ++ tailWord_3090930) baseStart_3090930 baseEnd_3090930 := by
    simpa [prefixWord, tailWord_3090930, baseEnd_3090930] using wordTrace_append hprefix tailTrace_3090930
  have hstable : (prefixWord ++ tailWord_3090930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090930).length < 2 ^ (prefixWord ++ tailWord_3090930).sum := by decide
  have hdescent : baseEnd_3090930 < baseStart_3090930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090934 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 2, 3]
def baseStart_3090934 : Nat := 118140960795 + 3090934 * 2 ^ 59
def prefixEnd_3090934 : Nat := 4983230072969 + 3 ^ 40 * 3090934 * 2
def baseEnd_3090934 : Nat := 1058089875549543293473373

theorem tailTrace_3090934 : CollatzResearch.WordTrace tailWord_3090934 prefixEnd_3090934 1058089875549543293473373 := by
  unfold tailWord_3090934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045976536505092646554991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75157083056054321563253237 7045976536505092646554991)
  ·
    refine ⟨10568964804757638969832487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7045976536505092646554991 10568964804757638969832487)
    ·
      refine ⟨15853447207136458454748731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10568964804757638969832487 15853447207136458454748731)
      ·
        refine ⟨23780170810704687682123097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15853447207136458454748731 23780170810704687682123097)
        ·
          refine ⟨17835128108028515761592323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23780170810704687682123097 17835128108028515761592323)
          ·
            refine ⟨26752692162042773642388485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17835128108028515761592323 26752692162042773642388485)
            ·
              refine ⟨5016129780383020057947841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26752692162042773642388485 5016129780383020057947841)
              ·
                refine ⟨3762097335287265043460881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5016129780383020057947841 3762097335287265043460881)
                ·
                  refine ⟨2821573001465448782595661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3762097335287265043460881 2821573001465448782595661)
                  ·
                    refine ⟨1058089875549543293473373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821573001465448782595661 1058089875549543293473373)
                    ·
                      rfl

theorem cell22_3090934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_3090934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090934 prefixEnd_3090934 := by exact prefixLift 3090934
  have htrace : WordTrace (prefixWord ++ tailWord_3090934) baseStart_3090934 baseEnd_3090934 := by
    simpa [prefixWord, tailWord_3090934, baseEnd_3090934] using wordTrace_append hprefix tailTrace_3090934
  have hstable : (prefixWord ++ tailWord_3090934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090934).length < 2 ^ (prefixWord ++ tailWord_3090934).sum := by decide
  have hdescent : baseEnd_3090934 < baseStart_3090934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090943 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 8]
def baseStart_3090943 : Nat := 118140960795 + 3090943 * 2 ^ 59
def prefixEnd_3090943 : Nat := 4983230072969 + 3 ^ 40 * 3090943 * 2
def baseEnd_3090943 : Nat := 1058092956433470269998345

theorem tailTrace_3090943 : CollatzResearch.WordTrace tailWord_3090943 prefixEnd_3090943 1058092956433470269998345 := by
  unfold tailWord_3090943
  simp only [CollatzResearch.WordTrace]
  refine ⟨112735952841048876881957483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75157301894032584587971655 112735952841048876881957483)
  ·
    refine ⟨169103929261573315322936225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112735952841048876881957483 169103929261573315322936225)
    ·
      refine ⟨126827946946179986492202169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169103929261573315322936225 126827946946179986492202169)
      ·
        refine ⟨95120960209634989869151627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126827946946179986492202169 95120960209634989869151627)
        ·
          refine ⟨142681440314452484803727441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95120960209634989869151627 142681440314452484803727441)
          ·
            refine ⟨107011080235839363602795581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142681440314452484803727441 107011080235839363602795581)
            ·
              refine ⟨40129155088439761351048343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107011080235839363602795581 40129155088439761351048343)
              ·
                refine ⟨60193732632659642026572515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40129155088439761351048343 60193732632659642026572515)
                ·
                  refine ⟨90290598948989463039858773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60193732632659642026572515 90290598948989463039858773)
                  ·
                    refine ⟨1058092956433470269998345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90290598948989463039858773 1058092956433470269998345)
                    ·
                      rfl

theorem cell22_3090943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_3090943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090943 prefixEnd_3090943 := by exact prefixLift 3090943
  have htrace : WordTrace (prefixWord ++ tailWord_3090943) baseStart_3090943 baseEnd_3090943 := by
    simpa [prefixWord, tailWord_3090943, baseEnd_3090943] using wordTrace_append hprefix tailTrace_3090943
  have hstable : (prefixWord ++ tailWord_3090943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090943).length < 2 ^ (prefixWord ++ tailWord_3090943).sum := by decide
  have hdescent : baseEnd_3090943 < baseStart_3090943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090964 : List Nat := [2, 4, 3, 1, 1, 2, 3, 6]
def baseStart_3090964 : Nat := 118140960795 + 3090964 * 2 ^ 59
def prefixEnd_3090964 : Nat := 4983230072969 + 3 ^ 40 * 3090964 * 2
def baseEnd_3090964 : Nat := 117566682795848135024809

theorem tailTrace_3090964 : CollatzResearch.WordTrace tailWord_3090964 prefixEnd_3090964 117566682795848135024809 := by
  unfold tailWord_3090964
  simp only [CollatzResearch.WordTrace]
  refine ⟨56368359386986398734235973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75157812515981864978981297 56368359386986398734235973)
  ·
    refine ⟨10569067385059949762669245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56368359386986398734235973 10569067385059949762669245)
    ·
      refine ⟨3963400269397481161000967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10569067385059949762669245 3963400269397481161000967)
      ·
        refine ⟨5945100404096221741501451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3963400269397481161000967 5945100404096221741501451)
        ·
          refine ⟨8917650606144332612252177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945100404096221741501451 8917650606144332612252177)
          ·
            refine ⟨6688237954608249459189133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8917650606144332612252177 6688237954608249459189133)
            ·
              refine ⟨2508089232978093547195925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6688237954608249459189133 2508089232978093547195925)
              ·
                refine ⟨117566682795848135024809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2508089232978093547195925 117566682795848135024809)
                ·
                  rfl

theorem cell22_3090964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 6].length) (baseStart_3090964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090964 prefixEnd_3090964 := by exact prefixLift 3090964
  have htrace : WordTrace (prefixWord ++ tailWord_3090964) baseStart_3090964 baseEnd_3090964 := by
    simpa [prefixWord, tailWord_3090964, baseEnd_3090964] using wordTrace_append hprefix tailTrace_3090964
  have hstable : (prefixWord ++ tailWord_3090964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090964).length < 2 ^ (prefixWord ++ tailWord_3090964).sum := by decide
  have hdescent : baseEnd_3090964 < baseStart_3090964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3090979 : List Nat := [1, 1, 1, 4, 4, 1, 1, 5, 1, 3]
def baseStart_3090979 : Nat := 118140960795 + 3090979 * 2 ^ 59
def prefixEnd_3090979 : Nat := 4983230072969 + 3 ^ 40 * 3090979 * 2
def baseEnd_3090979 : Nat := 1058105279969178176098235

theorem tailTrace_3090979 : CollatzResearch.WordTrace tailWord_3090979 prefixEnd_3090979 1058105279969178176098235 := by
  unfold tailWord_3090979
  simp only [CollatzResearch.WordTrace]
  refine ⟨112737265868918455030267991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75158177245945636686845327 112737265868918455030267991)
  ·
    refine ⟨169105898803377682545401987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112737265868918455030267991 169105898803377682545401987)
    ·
      refine ⟨253658848205066523818102981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169105898803377682545401987 253658848205066523818102981)
      ·
        refine ⟨47561034038449973215894309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253658848205066523818102981 47561034038449973215894309)
        ·
          refine ⟨8917693882209369977980183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47561034038449973215894309 8917693882209369977980183)
          ·
            refine ⟨13376540823314054966970275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8917693882209369977980183 13376540823314054966970275)
            ·
              refine ⟨20064811234971082450455413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13376540823314054966970275 20064811234971082450455413)
              ·
                refine ⟨1881076053278538979730195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20064811234971082450455413 1881076053278538979730195)
                ·
                  refine ⟨2821614079917808469595293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881076053278538979730195 2821614079917808469595293)
                  ·
                    refine ⟨1058105279969178176098235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821614079917808469595293 1058105279969178176098235)
                    ·
                      rfl

theorem cell22_3090979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5, 1, 3].length) (baseStart_3090979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3090979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3090979 prefixEnd_3090979 := by exact prefixLift 3090979
  have htrace : WordTrace (prefixWord ++ tailWord_3090979) baseStart_3090979 baseEnd_3090979 := by
    simpa [prefixWord, tailWord_3090979, baseEnd_3090979] using wordTrace_append hprefix tailTrace_3090979
  have hstable : (prefixWord ++ tailWord_3090979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3090979).length < 2 ^ (prefixWord ++ tailWord_3090979).sum := by decide
  have hdescent : baseEnd_3090979 < baseStart_3090979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3090979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091009 : List Nat := [1, 2, 5, 1, 1, 3, 3, 1, 5]
def baseStart_3091009 : Nat := 118140960795 + 3091009 * 2 ^ 59
def prefixEnd_3091009 : Nat := 4983230072969 + 3 ^ 40 * 3091009 * 2
def baseEnd_3091009 : Nat := 352705183194089365949381

theorem tailTrace_3091009 : CollatzResearch.WordTrace tailWord_3091009 prefixEnd_3091009 352705183194089365949381 := by
  unfold tailWord_3091009
  simp only [CollatzResearch.WordTrace]
  refine ⟨112738360058809770153860081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75158906705873180102573387 112738360058809770153860081)
  ·
    refine ⟨84553770044107327615395061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112738360058809770153860081 84553770044107327615395061)
    ·
      refine ⟨7926915941635061963943287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84553770044107327615395061 7926915941635061963943287)
      ·
        refine ⟨11890373912452592945914931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926915941635061963943287 11890373912452592945914931)
        ·
          refine ⟨17835560868678889418872397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11890373912452592945914931 17835560868678889418872397)
          ·
            refine ⟨6688335325754583532077149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17835560868678889418872397 6688335325754583532077149)
            ·
              refine ⟨2508125747157968824528931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6688335325754583532077149 2508125747157968824528931)
              ·
                refine ⟨3762188620736953236793397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508125747157968824528931 3762188620736953236793397)
                ·
                  refine ⟨352705183194089365949381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3762188620736953236793397 352705183194089365949381)
                  ·
                    rfl

theorem cell22_3091009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_3091009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091009 prefixEnd_3091009 := by exact prefixLift 3091009
  have htrace : WordTrace (prefixWord ++ tailWord_3091009) baseStart_3091009 baseEnd_3091009 := by
    simpa [prefixWord, tailWord_3091009, baseEnd_3091009] using wordTrace_append hprefix tailTrace_3091009
  have hstable : (prefixWord ++ tailWord_3091009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091009).length < 2 ^ (prefixWord ++ tailWord_3091009).sum := by decide
  have hdescent : baseEnd_3091009 < baseStart_3091009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091020 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 6]
def baseStart_3091020 : Nat := 118140960795 + 3091020 * 2 ^ 59
def prefixEnd_3091020 : Nat := 4983230072969 + 3 ^ 40 * 3091020 * 2
def baseEnd_3091020 : Nat := 352706438369022578607703

theorem tailTrace_3091020 : CollatzResearch.WordTrace tailWord_3091020 prefixEnd_3091020 352706438369022578607703 := by
  unfold tailWord_3091020
  simp only [CollatzResearch.WordTrace]
  refine ⟨56369380630884959516255257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75159174174513279355007009 56369380630884959516255257)
  ·
    refine ⟨42277035473163719637191443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56369380630884959516255257 42277035473163719637191443)
    ·
      refine ⟨63415553209745579455787165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42277035473163719637191443 63415553209745579455787165)
      ·
        refine ⟨23780832453654592295920187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63415553209745579455787165 23780832453654592295920187)
        ·
          refine ⟨35671248680481888443880281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23780832453654592295920187 35671248680481888443880281)
          ·
            refine ⟨26753436510361416332910211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35671248680481888443880281 26753436510361416332910211)
            ·
              refine ⟨40130154765542124499365317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26753436510361416332910211 40130154765542124499365317)
              ·
                refine ⟨7524404018539148343630997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40130154765542124499365317 7524404018539148343630997)
                ·
                  refine ⟨352706438369022578607703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7524404018539148343630997 352706438369022578607703)
                  ·
                    rfl

theorem cell22_3091020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_3091020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091020 prefixEnd_3091020 := by exact prefixLift 3091020
  have htrace : WordTrace (prefixWord ++ tailWord_3091020) baseStart_3091020 baseEnd_3091020 := by
    simpa [prefixWord, tailWord_3091020, baseEnd_3091020] using wordTrace_append hprefix tailTrace_3091020
  have hstable : (prefixWord ++ tailWord_3091020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091020).length < 2 ^ (prefixWord ++ tailWord_3091020).sum := by decide
  have hdescent : baseEnd_3091020 < baseStart_3091020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091022 : List Nat := [4, 1, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3091022 : Nat := 118140960795 + 3091022 * 2 ^ 59
def prefixEnd_3091022 : Nat := 4983230072969 + 3 ^ 40 * 3091022 * 2
def baseEnd_3091022 : Nat := 1058119999747940397273103

theorem tailTrace_3091022 : CollatzResearch.WordTrace tailWord_3091022 prefixEnd_3091022 1058119999747940397273103 := by
  unfold tailWord_3091022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092354275970334171760415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75159222805175115582722213 14092354275970334171760415)
  ·
    refine ⟨21138531413955501257640623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14092354275970334171760415 21138531413955501257640623)
    ·
      refine ⟨31707797120933251886460935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21138531413955501257640623 31707797120933251886460935)
      ·
        refine ⟨47561695681399877829691403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31707797120933251886460935 47561695681399877829691403)
        ·
          refine ⟨71342543522099816744537105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47561695681399877829691403 71342543522099816744537105)
          ·
            refine ⟨53506907641574862558402829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71342543522099816744537105 53506907641574862558402829)
            ·
              refine ⟨20065090365590573459401061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53506907641574862558402829 20065090365590573459401061)
              ·
                refine ⟨3762204443548232523637699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20065090365590573459401061 3762204443548232523637699)
                ·
                  refine ⟨5643306665322348785456549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762204443548232523637699 5643306665322348785456549)
                  ·
                    refine ⟨1058119999747940397273103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5643306665322348785456549 1058119999747940397273103)
                    ·
                      rfl

theorem cell22_3091022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3091022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091022 prefixEnd_3091022 := by exact prefixLift 3091022
  have htrace : WordTrace (prefixWord ++ tailWord_3091022) baseStart_3091022 baseEnd_3091022 := by
    simpa [prefixWord, tailWord_3091022, baseEnd_3091022] using wordTrace_append hprefix tailTrace_3091022
  have hstable : (prefixWord ++ tailWord_3091022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091022).length < 2 ^ (prefixWord ++ tailWord_3091022).sum := by decide
  have hdescent : baseEnd_3091022 < baseStart_3091022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091052 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_3091052 : Nat := 118140960795 + 3091052 * 2 ^ 59
def prefixEnd_3091052 : Nat := 4983230072969 + 3 ^ 40 * 3091052 * 2
def baseEnd_3091052 : Nat := 1058130269361030319023011

theorem tailTrace_3091052 : CollatzResearch.WordTrace tailWord_3091052 prefixEnd_3091052 1058130269361030319023011 := by
  unfold tailWord_3091052
  simp only [CollatzResearch.WordTrace]
  refine ⟨56369964198826994248837705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75159952265102658998450273 56369964198826994248837705)
  ·
    refine ⟨42277473149120245686628279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56369964198826994248837705 42277473149120245686628279)
    ·
      refine ⟨63416209723680368529942419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42277473149120245686628279 63416209723680368529942419)
      ·
        refine ⟨95124314585520552794913629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63416209723680368529942419 95124314585520552794913629)
        ·
          refine ⟨35671617969570207298092611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95124314585520552794913629 35671617969570207298092611)
          ·
            refine ⟨53507426954355310947138917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35671617969570207298092611 53507426954355310947138917)
            ·
              refine ⟨10032642553941620802588547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53507426954355310947138917 10032642553941620802588547)
              ·
                refine ⟨15048963830912431203882821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10032642553941620802588547 15048963830912431203882821)
                ·
                  refine ⟨2821680718296080850728029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15048963830912431203882821 2821680718296080850728029)
                  ·
                    refine ⟨1058130269361030319023011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821680718296080850728029 1058130269361030319023011)
                    ·
                      rfl

theorem cell22_3091052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_3091052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091052 prefixEnd_3091052 := by exact prefixLift 3091052
  have htrace : WordTrace (prefixWord ++ tailWord_3091052) baseStart_3091052 baseEnd_3091052 := by
    simpa [prefixWord, tailWord_3091052, baseEnd_3091052] using wordTrace_append hprefix tailTrace_3091052
  have hstable : (prefixWord ++ tailWord_3091052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091052).length < 2 ^ (prefixWord ++ tailWord_3091052).sum := by decide
  have hdescent : baseEnd_3091052 < baseStart_3091052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091054 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_3091054 : Nat := 118140960795 + 3091054 * 2 ^ 59
def prefixEnd_3091054 : Nat := 4983230072969 + 3 ^ 40 * 3091054 * 2
def baseEnd_3091054 : Nat := 352710318000634326824335

theorem tailTrace_3091054 : CollatzResearch.WordTrace tailWord_3091054 prefixEnd_3091054 352710318000634326824335 := by
  unfold tailWord_3091054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14092500167955842854906027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75160000895764495226165477 14092500167955842854906027)
  ·
    refine ⟨21138750251933764282359041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14092500167955842854906027 21138750251933764282359041)
    ·
      refine ⟨15854062688950323211769281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21138750251933764282359041 15854062688950323211769281)
      ·
        refine ⟨11890547016712742408826961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15854062688950323211769281 11890547016712742408826961)
        ·
          refine ⟨8917910262534556806620221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11890547016712742408826961 8917910262534556806620221)
          ·
            refine ⟨3344216348450458802482583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8917910262534556806620221 3344216348450458802482583)
            ·
              refine ⟨5016324522675688203723875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3344216348450458802482583 5016324522675688203723875)
              ·
                refine ⟨7524486784013532305585813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5016324522675688203723875 7524486784013532305585813)
                ·
                  refine ⟨352710318000634326824335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7524486784013532305585813 352710318000634326824335)
                  ·
                    rfl

theorem cell22_3091054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_3091054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091054 prefixEnd_3091054 := by exact prefixLift 3091054
  have htrace : WordTrace (prefixWord ++ tailWord_3091054) baseStart_3091054 baseEnd_3091054 := by
    simpa [prefixWord, tailWord_3091054, baseEnd_3091054] using wordTrace_append hprefix tailTrace_3091054
  have hstable : (prefixWord ++ tailWord_3091054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091054).length < 2 ^ (prefixWord ++ tailWord_3091054).sum := by decide
  have hdescent : baseEnd_3091054 < baseStart_3091054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091065 : List Nat := [1, 2, 1, 3, 3, 2, 1, 9]
def baseStart_3091065 : Nat := 118140960795 + 3091065 * 2 ^ 59
def prefixEnd_3091065 : Nat := 4983230072969 + 3 ^ 40 * 3091065 * 2
def baseEnd_3091065 : Nat := 117570524391855846494219

theorem tailTrace_3091065 : CollatzResearch.WordTrace tailWord_3091065 prefixEnd_3091065 117570524391855846494219 := by
  unfold tailWord_3091065
  simp only [CollatzResearch.WordTrace]
  refine ⟨112740402546606891717898649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75160268364404594478599099 112740402546606891717898649)
  ·
    refine ⟨84555301909955168788423987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112740402546606891717898649 84555301909955168788423987)
    ·
      refine ⟨126832952864932753182635981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84555301909955168788423987 126832952864932753182635981)
      ·
        refine ⟨47562357324349782443488493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126832952864932753182635981 47562357324349782443488493)
        ·
          refine ⟨17835883996631168416308185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47562357324349782443488493 17835883996631168416308185)
          ·
            refine ⟨13376912997473376312231139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17835883996631168416308185 13376912997473376312231139)
            ·
              refine ⟨20065369496210064468346709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13376912997473376312231139 20065369496210064468346709)
              ·
                refine ⟨117570524391855846494219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20065369496210064468346709 117570524391855846494219)
                ·
                  rfl

theorem cell22_3091065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 9].length) (baseStart_3091065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091065 prefixEnd_3091065 := by exact prefixLift 3091065
  have htrace : WordTrace (prefixWord ++ tailWord_3091065) baseStart_3091065 baseEnd_3091065 := by
    simpa [prefixWord, tailWord_3091065, baseEnd_3091065] using wordTrace_append hprefix tailTrace_3091065
  have hstable : (prefixWord ++ tailWord_3091065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091065).length < 2 ^ (prefixWord ++ tailWord_3091065).sum := by decide
  have hdescent : baseEnd_3091065 < baseStart_3091065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091148 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_3091148 : Nat := 118140960795 + 3091148 * 2 ^ 59
def prefixEnd_3091148 : Nat := 4983230072969 + 3 ^ 40 * 3091148 * 2
def baseEnd_3091148 : Nat := 1058163132122918068622717

theorem tailTrace_3091148 : CollatzResearch.WordTrace tailWord_3091148 prefixEnd_3091148 1058163132122918068622717 := by
  unfold tailWord_3091148
  simp only [CollatzResearch.WordTrace]
  refine ⟨56371714902653098446585049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75162286536870797928780065 56371714902653098446585049)
  ·
    refine ⟨42278786176989823834938787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56371714902653098446585049 42278786176989823834938787)
    ·
      refine ⟨63418179265484735752408181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42278786176989823834938787 63418179265484735752408181)
      ·
        refine ⟨5945454306139193976788267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63418179265484735752408181 5945454306139193976788267)
        ·
          refine ⟨8918181459208790965182401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5945454306139193976788267 8918181459208790965182401)
          ·
            refine ⟨6688636094406593223886801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8918181459208790965182401 6688636094406593223886801)
            ·
              refine ⟨5016477070804944917915101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6688636094406593223886801 5016477070804944917915101)
              ·
                refine ⟨1881178901551854344218163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5016477070804944917915101 1881178901551854344218163)
                ·
                  refine ⟨2821768352327781516327245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881178901551854344218163 2821768352327781516327245)
                  ·
                    refine ⟨1058163132122918068622717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821768352327781516327245 1058163132122918068622717)
                    ·
                      rfl

theorem cell22_3091148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_3091148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091148 prefixEnd_3091148 := by exact prefixLift 3091148
  have htrace : WordTrace (prefixWord ++ tailWord_3091148) baseStart_3091148 baseEnd_3091148 := by
    simpa [prefixWord, tailWord_3091148, baseEnd_3091148] using wordTrace_append hprefix tailTrace_3091148
  have hstable : (prefixWord ++ tailWord_3091148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091148).length < 2 ^ (prefixWord ++ tailWord_3091148).sum := by decide
  have hdescent : baseEnd_3091148 < baseStart_3091148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091172 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_3091172 : Nat := 118140960795 + 3091172 * 2 ^ 59
def prefixEnd_3091172 : Nat := 4983230072969 + 3 ^ 40 * 3091172 * 2
def baseEnd_3091172 : Nat := 352723782604463335340881

theorem tailTrace_3091172 : CollatzResearch.WordTrace tailWord_3091172 prefixEnd_3091172 352723782604463335340881 := by
  unfold tailWord_3091172
  simp only [CollatzResearch.WordTrace]
  refine ⟨56372152578609624496021885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75162870104812832661362513 56372152578609624496021885)
  ·
    refine ⟨21139557216978609186008207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56372152578609624496021885 21139557216978609186008207)
    ·
      refine ⟨31709335825467913779012311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21139557216978609186008207 31709335825467913779012311)
      ·
        refine ⟨47564003738201870668518467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31709335825467913779012311 47564003738201870668518467)
        ·
          refine ⟨71346005607302806002777701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47564003738201870668518467 71346005607302806002777701)
          ·
            refine ⟨13377376051369276125520819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71346005607302806002777701 13377376051369276125520819)
            ·
              refine ⟨20066064077053914188281229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13377376051369276125520819 20066064077053914188281229)
              ·
                refine ⟨7524774028895217820605461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20066064077053914188281229 7524774028895217820605461)
                ·
                  refine ⟨352723782604463335340881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7524774028895217820605461 352723782604463335340881)
                  ·
                    rfl

theorem cell22_3091172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_3091172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091172 prefixEnd_3091172 := by exact prefixLift 3091172
  have htrace : WordTrace (prefixWord ++ tailWord_3091172) baseStart_3091172 baseEnd_3091172 := by
    simpa [prefixWord, tailWord_3091172, baseEnd_3091172] using wordTrace_append hprefix tailTrace_3091172
  have hstable : (prefixWord ++ tailWord_3091172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091172).length < 2 ^ (prefixWord ++ tailWord_3091172).sum := by decide
  have hdescent : baseEnd_3091172 < baseStart_3091172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091204 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_3091204 : Nat := 118140960795 + 3091204 * 2 ^ 59
def prefixEnd_3091204 : Nat := 4983230072969 + 3 ^ 40 * 3091204 * 2
def baseEnd_3091204 : Nat := 1058182302067352589222545

theorem tailTrace_3091204 : CollatzResearch.WordTrace tailWord_3091204 prefixEnd_3091204 1058182302067352589222545 := by
  unfold tailWord_3091204
  simp only [CollatzResearch.WordTrace]
  refine ⟨56372736146551659228604333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75163648195402212304805777 56372736146551659228604333)
  ·
    refine ⟨21139776054956872210726625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56372736146551659228604333 21139776054956872210726625)
    ·
      refine ⟨15854832041217654158044969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21139776054956872210726625 15854832041217654158044969)
      ·
        refine ⟨11891124030913240618533727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15854832041217654158044969 11891124030913240618533727)
        ·
          refine ⟨17836686046369860927800591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11891124030913240618533727 17836686046369860927800591)
          ·
            refine ⟨26755029069554791391700887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17836686046369860927800591 26755029069554791391700887)
            ·
              refine ⟨40132543604332187087551331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26755029069554791391700887 40132543604332187087551331)
              ·
                refine ⟨60198815406498280631326997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40132543604332187087551331 60198815406498280631326997)
                ·
                  refine ⟨2821819472179606904593453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60198815406498280631326997 2821819472179606904593453)
                  ·
                    refine ⟨1058182302067352589222545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821819472179606904593453 1058182302067352589222545)
                    ·
                      rfl

theorem cell22_3091204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_3091204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091204 prefixEnd_3091204 := by exact prefixLift 3091204
  have htrace : WordTrace (prefixWord ++ tailWord_3091204) baseStart_3091204 baseEnd_3091204 := by
    simpa [prefixWord, tailWord_3091204, baseEnd_3091204] using wordTrace_append hprefix tailTrace_3091204
  have hstable : (prefixWord ++ tailWord_3091204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091204).length < 2 ^ (prefixWord ++ tailWord_3091204).sum := by decide
  have hdescent : baseEnd_3091204 < baseStart_3091204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091223 : List Nat := [1, 1, 3, 4, 3, 1, 3, 2, 4]
def baseStart_3091223 : Nat := 118140960795 + 3091223 * 2 ^ 59
def prefixEnd_3091223 : Nat := 4983230072969 + 3 ^ 40 * 3091223 * 2
def baseEnd_3091223 : Nat := 352729602051880957665829

theorem tailTrace_3091223 : CollatzResearch.WordTrace tailWord_3091223 prefixEnd_3091223 352729602051880957665829 := by
  unfold tailWord_3091223
  simp only [CollatzResearch.WordTrace]
  refine ⟨112746165280034484702150323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75164110186689656468100215 112746165280034484702150323)
  ·
    refine ⟨169119247920051727053225485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112746165280034484702150323 169119247920051727053225485)
    ·
      refine ⟨63419717970019397644959557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169119247920051727053225485 63419717970019397644959557)
      ·
        refine ⟨11891197119378637058429917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63419717970019397644959557 11891197119378637058429917)
        ·
          refine ⟨4459198919766988896911219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11891197119378637058429917 4459198919766988896911219)
          ·
            refine ⟨6688798379650483345366829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459198919766988896911219 6688798379650483345366829)
            ·
              refine ⟨2508299392368931254512561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6688798379650483345366829 2508299392368931254512561)
              ·
                refine ⟨1881224544276698440884421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508299392368931254512561 1881224544276698440884421)
                ·
                  refine ⟨352729602051880957665829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881224544276698440884421 352729602051880957665829)
                  ·
                    rfl

theorem cell22_3091223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 4].length) (baseStart_3091223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091223 prefixEnd_3091223 := by exact prefixLift 3091223
  have htrace : WordTrace (prefixWord ++ tailWord_3091223) baseStart_3091223 baseEnd_3091223 := by
    simpa [prefixWord, tailWord_3091223, baseEnd_3091223] using wordTrace_append hprefix tailTrace_3091223
  have hstable : (prefixWord ++ tailWord_3091223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091223).length < 2 ^ (prefixWord ++ tailWord_3091223).sum := by decide
  have hdescent : baseEnd_3091223 < baseStart_3091223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091234 : List Nat := [3, 3, 1, 1, 2, 3, 2, 7]
def baseStart_3091234 : Nat := 118140960795 + 3091234 * 2 ^ 59
def prefixEnd_3091234 : Nat := 4983230072969 + 3 ^ 40 * 3091234 * 2
def baseEnd_3091234 : Nat := 117576952408938056774717

theorem tailTrace_3091234 : CollatzResearch.WordTrace tailWord_3091234 prefixEnd_3091234 117576952408938056774717 := by
  unfold tailWord_3091234
  simp only [CollatzResearch.WordTrace]
  refine ⟨28186641620748658395200189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75164377655329755720533837 28186641620748658395200189)
  ·
    refine ⟨10569990607780746898200071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28186641620748658395200189 10569990607780746898200071)
    ·
      refine ⟨15854985911671120347300107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10569990607780746898200071 15854985911671120347300107)
      ·
        refine ⟨23782478867506680520950161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15854985911671120347300107 23782478867506680520950161)
        ·
          refine ⟨17836859150630010390712621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23782478867506680520950161 17836859150630010390712621)
          ·
            refine ⟨6688822181486253896517233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17836859150630010390712621 6688822181486253896517233)
            ·
              refine ⟨5016616636114690422387925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6688822181486253896517233 5016616636114690422387925)
              ·
                refine ⟨117576952408938056774717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5016616636114690422387925 117576952408938056774717)
                ·
                  rfl

theorem cell22_3091234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_3091234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091234 prefixEnd_3091234 := by exact prefixLift 3091234
  have htrace : WordTrace (prefixWord ++ tailWord_3091234) baseStart_3091234 baseEnd_3091234 := by
    simpa [prefixWord, tailWord_3091234, baseEnd_3091234] using wordTrace_append hprefix tailTrace_3091234
  have hstable : (prefixWord ++ tailWord_3091234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091234).length < 2 ^ (prefixWord ++ tailWord_3091234).sum := by decide
  have hdescent : baseEnd_3091234 < baseStart_3091234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091249 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_3091249 : Nat := 118140960795 + 3091249 * 2 ^ 59
def prefixEnd_3091249 : Nat := 4983230072969 + 3 ^ 40 * 3091249 * 2
def baseEnd_3091249 : Nat := 1058197706486987471847407

theorem tailTrace_3091249 : CollatzResearch.WordTrace tailWord_3091249 prefixEnd_3091249 1058197706486987471847407 := by
  unfold tailWord_3091249
  simp only [CollatzResearch.WordTrace]
  refine ⟨112747113577940291142596801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75164742385293527428397867 112747113577940291142596801)
  ·
    refine ⟨84560335183455218356947601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112747113577940291142596801 84560335183455218356947601)
    ·
      refine ⟨63420251387591413767710701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84560335183455218356947601 63420251387591413767710701)
      ·
        refine ⟨23782594270346780162891513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63420251387591413767710701 23782594270346780162891513)
        ·
          refine ⟨17836945702760085122168635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23782594270346780162891513 17836945702760085122168635)
          ·
            refine ⟨26755418554140127683252953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17836945702760085122168635 26755418554140127683252953)
            ·
              refine ⟨20066563915605095762439715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26755418554140127683252953 20066563915605095762439715)
              ·
                refine ⟨30099845873407643643659573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20066563915605095762439715 30099845873407643643659573)
                ·
                  refine ⟨2821860550631966591593085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30099845873407643643659573 2821860550631966591593085)
                  ·
                    refine ⟨1058197706486987471847407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2821860550631966591593085 1058197706486987471847407)
                    ·
                      rfl

theorem cell22_3091249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_3091249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091249 prefixEnd_3091249 := by exact prefixLift 3091249
  have htrace : WordTrace (prefixWord ++ tailWord_3091249) baseStart_3091249 baseEnd_3091249 := by
    simpa [prefixWord, tailWord_3091249, baseEnd_3091249] using wordTrace_append hprefix tailTrace_3091249
  have hstable : (prefixWord ++ tailWord_3091249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091249).length < 2 ^ (prefixWord ++ tailWord_3091249).sum := by decide
  have hdescent : baseEnd_3091249 < baseStart_3091249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091307 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 8]
def baseStart_3091307 : Nat := 118140960795 + 3091307 * 2 ^ 59
def prefixEnd_3091307 : Nat := 4983230072969 + 3 ^ 40 * 3091307 * 2
def baseEnd_3091307 : Nat := 352739187024098217965743

theorem tailTrace_3091307 : CollatzResearch.WordTrace tailWord_3091307 prefixEnd_3091307 352739187024098217965743 := by
  unfold tailWord_3091307
  simp only [CollatzResearch.WordTrace]
  refine ⟨112749229011730167048208175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75166152674486778032138783 112749229011730167048208175)
  ·
    refine ⟨169123843517595250572312263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112749229011730167048208175 169123843517595250572312263)
    ·
      refine ⟨253685765276392875858468395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169123843517595250572312263 253685765276392875858468395)
      ·
        refine ⟨380528647914589313787702593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253685765276392875858468395 380528647914589313787702593)
        ·
          refine ⟨285396485935941985340776945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380528647914589313787702593 285396485935941985340776945)
          ·
            refine ⟨214047364451956489005582709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 285396485935941985340776945 214047364451956489005582709)
            ·
              refine ⟨20066940417370920844273379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214047364451956489005582709 20066940417370920844273379)
              ·
                refine ⟨30100410626056381266410069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20066940417370920844273379 30100410626056381266410069)
                ·
                  refine ⟨352739187024098217965743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30100410626056381266410069 352739187024098217965743)
                  ·
                    rfl

theorem cell22_3091307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_3091307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091307 prefixEnd_3091307 := by exact prefixLift 3091307
  have htrace : WordTrace (prefixWord ++ tailWord_3091307) baseStart_3091307 baseEnd_3091307 := by
    simpa [prefixWord, tailWord_3091307, baseEnd_3091307] using wordTrace_append hprefix tailTrace_3091307
  have hstable : (prefixWord ++ tailWord_3091307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091307).length < 2 ^ (prefixWord ++ tailWord_3091307).sum := by decide
  have hdescent : baseEnd_3091307 < baseStart_3091307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091452 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_3091452 : Nat := 118140960795 + 3091452 * 2 ^ 59
def prefixEnd_3091452 : Nat := 4983230072969 + 3 ^ 40 * 3091452 * 2
def baseEnd_3091452 : Nat := 1058267197535562609021785

theorem tailTrace_3091452 : CollatzResearch.WordTrace tailWord_3091452 prefixEnd_3091452 1058267197535562609021785 := by
  unfold tailWord_3091452
  simp only [CollatzResearch.WordTrace]
  refine ⟨56377258798102428406118305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75169678397469904541491073 56377258798102428406118305)
  ·
    refine ⟨42282944098576821304588729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56377258798102428406118305 42282944098576821304588729)
    ·
      refine ⟨31712208073932615978441547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42282944098576821304588729 31712208073932615978441547)
      ·
        refine ⟨47568312110898923967662321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31712208073932615978441547 47568312110898923967662321)
        ·
          refine ⟨35676234083174192975746741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47568312110898923967662321 35676234083174192975746741)
          ·
            refine ⟨3344646945297580591476257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35676234083174192975746741 3344646945297580591476257)
            ·
              refine ⟨2508485208973185443607193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3344646945297580591476257 2508485208973185443607193)
              ·
                refine ⟨1881363906729889082705395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508485208973185443607193 1881363906729889082705395)
                ·
                  refine ⟨2822045860094833624058093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881363906729889082705395 2822045860094833624058093)
                  ·
                    refine ⟨1058267197535562609021785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822045860094833624058093 1058267197535562609021785)
                    ·
                      rfl

theorem cell22_3091452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_3091452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091452 prefixEnd_3091452 := by exact prefixLift 3091452
  have htrace : WordTrace (prefixWord ++ tailWord_3091452) baseStart_3091452 baseEnd_3091452 := by
    simpa [prefixWord, tailWord_3091452, baseEnd_3091452] using wordTrace_append hprefix tailTrace_3091452
  have hstable : (prefixWord ++ tailWord_3091452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091452).length < 2 ^ (prefixWord ++ tailWord_3091452).sum := by decide
  have hdescent : baseEnd_3091452 < baseStart_3091452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091491 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 1, 5]
def baseStart_3091491 : Nat := 118140960795 + 3091491 * 2 ^ 59
def prefixEnd_3091491 : Nat := 4983230072969 + 3 ^ 40 * 3091491 * 2
def baseEnd_3091491 : Nat := 1058280548032579507296665

theorem tailTrace_3091491 : CollatzResearch.WordTrace tailWord_3091491 prefixEnd_3091491 1058280548032579507296665 := by
  unfold tailWord_3091491
  simp only [CollatzResearch.WordTrace]
  refine ⟨112755940043063566472906327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75170626695375710981937551 112755940043063566472906327)
  ·
    refine ⟨169133910064595349709359491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112755940043063566472906327 169133910064595349709359491)
    ·
      refine ⟨253700865096893024564039237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169133910064595349709359491 253700865096893024564039237)
      ·
        refine ⟨47568912205667442105757357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253700865096893024564039237 47568912205667442105757357)
        ·
          refine ⟨17838342077125290789659009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47568912205667442105757357 17838342077125290789659009)
          ·
            refine ⟨13378756557843968092244257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17838342077125290789659009 13378756557843968092244257)
            ·
              refine ⟨10034067418382976069183193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13378756557843968092244257 10034067418382976069183193)
              ·
                refine ⟨7525550563787232051887395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10034067418382976069183193 7525550563787232051887395)
                ·
                  refine ⟨11288325845680848077831093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7525550563787232051887395 11288325845680848077831093)
                  ·
                    refine ⟨1058280548032579507296665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11288325845680848077831093 1058280548032579507296665)
                    ·
                      rfl

theorem cell22_3091491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 5].length) (baseStart_3091491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091491 prefixEnd_3091491 := by exact prefixLift 3091491
  have htrace : WordTrace (prefixWord ++ tailWord_3091491) baseStart_3091491 baseEnd_3091491 := by
    simpa [prefixWord, tailWord_3091491, baseEnd_3091491] using wordTrace_append hprefix tailTrace_3091491
  have hstable : (prefixWord ++ tailWord_3091491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091491).length < 2 ^ (prefixWord ++ tailWord_3091491).sum := by decide
  have hdescent : baseEnd_3091491 < baseStart_3091491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091493 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 4]
def baseStart_3091493 : Nat := 118140960795 + 3091493 * 2 ^ 59
def prefixEnd_3091493 : Nat := 4983230072969 + 3 ^ 40 * 3091493 * 2
def baseEnd_3091493 : Nat := 352760410891150722915553

theorem tailTrace_3091493 : CollatzResearch.WordTrace tailWord_3091493 prefixEnd_3091493 352760410891150722915553 := by
  unfold tailWord_3091493
  simp only [CollatzResearch.WordTrace]
  refine ⟨112756012989056320814479133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75170675326037547209652755 112756012989056320814479133)
  ·
    refine ⟨42283504870896120305429675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112756012989056320814479133 42283504870896120305429675)
    ·
      refine ⟨63425257306344180458144513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42283504870896120305429675 63425257306344180458144513)
      ·
        refine ⟨47568942979758135343608385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63425257306344180458144513 47568942979758135343608385)
        ·
          refine ⟨35676707234818601507706289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47568942979758135343608385 35676707234818601507706289)
          ·
            refine ⟨26757530426113951130779717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35676707234818601507706289 26757530426113951130779717)
            ·
              refine ⟨5017036954896365837021197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26757530426113951130779717 5017036954896365837021197)
              ·
                refine ⟨1881388858086137188882949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5017036954896365837021197 1881388858086137188882949)
                ·
                  refine ⟨352760410891150722915553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881388858086137188882949 352760410891150722915553)
                  ·
                    rfl

theorem cell22_3091493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_3091493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091493 prefixEnd_3091493 := by exact prefixLift 3091493
  have htrace : WordTrace (prefixWord ++ tailWord_3091493) baseStart_3091493 baseEnd_3091493 := by
    simpa [prefixWord, tailWord_3091493, baseEnd_3091493] using wordTrace_append hprefix tailTrace_3091493
  have hstable : (prefixWord ++ tailWord_3091493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091493).length < 2 ^ (prefixWord ++ tailWord_3091493).sum := by decide
  have hdescent : baseEnd_3091493 < baseStart_3091493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091495 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3091495 : Nat := 118140960795 + 3091495 * 2 ^ 59
def prefixEnd_3091495 : Nat := 4983230072969 + 3 ^ 40 * 3091495 * 2
def baseEnd_3091495 : Nat := 1058281917314324830196653

theorem tailTrace_3091495 : CollatzResearch.WordTrace tailWord_3091495 prefixEnd_3091495 1058281917314324830196653 := by
  unfold tailWord_3091495
  simp only [CollatzResearch.WordTrace]
  refine ⟨112756085935049075156051939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75170723956699383437367959 112756085935049075156051939)
  ·
    refine ⟨169134128902573612734077909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112756085935049075156051939 169134128902573612734077909)
    ·
      refine ⟨3964081146154069048454951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 169134128902573612734077909 3964081146154069048454951)
      ·
        refine ⟨5946121719231103572682427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964081146154069048454951 5946121719231103572682427)
        ·
          refine ⟨8919182578846655359023641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946121719231103572682427 8919182578846655359023641)
          ·
            refine ⟨6689386934134991519267731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8919182578846655359023641 6689386934134991519267731)
            ·
              refine ⟨10034080401202487278901597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689386934134991519267731 10034080401202487278901597)
              ·
                refine ⟨3762780150450932729588099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10034080401202487278901597 3762780150450932729588099)
                ·
                  refine ⟨5644170225676399094382149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3762780150450932729588099 5644170225676399094382149)
                  ·
                    refine ⟨1058281917314324830196653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5644170225676399094382149 1058281917314324830196653)
                    ·
                      rfl

theorem cell22_3091495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3091495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091495 prefixEnd_3091495 := by exact prefixLift 3091495
  have htrace : WordTrace (prefixWord ++ tailWord_3091495) baseStart_3091495 baseEnd_3091495 := by
    simpa [prefixWord, tailWord_3091495, baseEnd_3091495] using wordTrace_append hprefix tailTrace_3091495
  have hstable : (prefixWord ++ tailWord_3091495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091495).length < 2 ^ (prefixWord ++ tailWord_3091495).sum := by decide
  have hdescent : baseEnd_3091495 < baseStart_3091495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091504 : List Nat := [2, 1, 1, 1, 2, 4, 11]
def baseStart_3091504 : Nat := 118140960795 + 3091504 * 2 ^ 59
def prefixEnd_3091504 : Nat := 4983230072969 + 3 ^ 40 * 3091504 * 2
def baseEnd_3091504 : Nat := 39195740674009326174875

theorem tailTrace_3091504 : CollatzResearch.WordTrace tailWord_3091504 prefixEnd_3091504 39195740674009326174875 := by
  unfold tailWord_3091504
  simp only [CollatzResearch.WordTrace]
  refine ⟨56378207096008234846564783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75170942794677646462086377 56378207096008234846564783)
  ·
    refine ⟨84567310644012352269847175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56378207096008234846564783 84567310644012352269847175)
    ·
      refine ⟨126850965966018528404770763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84567310644012352269847175 126850965966018528404770763)
      ·
        refine ⟨190276448949027792607156145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126850965966018528404770763 190276448949027792607156145)
        ·
          refine ⟨142707336711770844455367109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190276448949027792607156145 142707336711770844455367109)
          ·
            refine ⟨26757625633457033335381333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142707336711770844455367109 26757625633457033335381333)
            ·
              refine ⟨39195740674009326174875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26757625633457033335381333 39195740674009326174875)
              ·
                rfl

theorem cell22_3091504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 11].length) (baseStart_3091504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091504 prefixEnd_3091504 := by exact prefixLift 3091504
  have htrace : WordTrace (prefixWord ++ tailWord_3091504) baseStart_3091504 baseEnd_3091504 := by
    simpa [prefixWord, tailWord_3091504, baseEnd_3091504] using wordTrace_append hprefix tailTrace_3091504
  have hstable : (prefixWord ++ tailWord_3091504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091504).length < 2 ^ (prefixWord ++ tailWord_3091504).sum := by decide
  have hdescent : baseEnd_3091504 < baseStart_3091504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091506 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_3091506 : Nat := 118140960795 + 3091506 * 2 ^ 59
def prefixEnd_3091506 : Nat := 4983230072969 + 3 ^ 40 * 3091506 * 2
def baseEnd_3091506 : Nat := 1058285682839124468171619

theorem tailTrace_3091506 : CollatzResearch.WordTrace tailWord_3091506 prefixEnd_3091506 1058285682839124468171619 := by
  unfold tailWord_3091506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28189121784502306008675593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75170991425339482689801581 28189121784502306008675593)
  ·
    refine ⟨21141841338376729506506695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28189121784502306008675593 21141841338376729506506695)
    ·
      refine ⟨31712762007565094259760043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21141841338376729506506695 31712762007565094259760043)
      ·
        refine ⟨47569143011347641389640065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31712762007565094259760043 47569143011347641389640065)
        ·
          refine ⟨35676857258510731042230049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47569143011347641389640065 35676857258510731042230049)
          ·
            refine ⟨26757642943883048281672537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35676857258510731042230049 26757642943883048281672537)
            ·
              refine ⟨20068232207912286211254403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26757642943883048281672537 20068232207912286211254403)
              ·
                refine ⟨30102348311868429316881605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20068232207912286211254403 30102348311868429316881605)
                ·
                  refine ⟨5644190308475330496915301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30102348311868429316881605 5644190308475330496915301)
                  ·
                    refine ⟨1058285682839124468171619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5644190308475330496915301 1058285682839124468171619)
                    ·
                      rfl

theorem cell22_3091506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_3091506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091506 prefixEnd_3091506 := by exact prefixLift 3091506
  have htrace : WordTrace (prefixWord ++ tailWord_3091506) baseStart_3091506 baseEnd_3091506 := by
    simpa [prefixWord, tailWord_3091506, baseEnd_3091506] using wordTrace_append hprefix tailTrace_3091506
  have hstable : (prefixWord ++ tailWord_3091506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091506).length < 2 ^ (prefixWord ++ tailWord_3091506).sum := by decide
  have hdescent : baseEnd_3091506 < baseStart_3091506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091510 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 4]
def baseStart_3091510 : Nat := 118140960795 + 3091510 * 2 ^ 59
def prefixEnd_3091510 : Nat := 4983230072969 + 3 ^ 40 * 3091510 * 2
def baseEnd_3091510 : Nat := 352762350706956597023869

theorem tailTrace_3091510 : CollatzResearch.WordTrace tailWord_3091510 prefixEnd_3091510 352762350706956597023869 := by
  unfold tailWord_3091510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7047289564374670794865499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75171088686663155145231989 7047289564374670794865499)
  ·
    refine ⟨10570934346562006192298249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7047289564374670794865499 10570934346562006192298249)
    ·
      refine ⟨7928200759921504644223687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10570934346562006192298249 7928200759921504644223687)
      ·
        refine ⟨11892301139882256966335531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7928200759921504644223687 11892301139882256966335531)
        ·
          refine ⟨17838451709823385449503297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11892301139882256966335531 17838451709823385449503297)
          ·
            refine ⟨13378838782367539087127473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17838451709823385449503297 13378838782367539087127473)
            ·
              refine ⟨10034129086775654315345605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13378838782367539087127473 10034129086775654315345605)
              ·
                refine ⟨1881399203770435184127301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10034129086775654315345605 1881399203770435184127301)
                ·
                  refine ⟨352762350706956597023869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881399203770435184127301 352762350706956597023869)
                  ·
                    rfl

theorem cell22_3091510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_3091510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091510 prefixEnd_3091510 := by exact prefixLift 3091510
  have htrace : WordTrace (prefixWord ++ tailWord_3091510) baseStart_3091510 baseEnd_3091510 := by
    simpa [prefixWord, tailWord_3091510, baseEnd_3091510] using wordTrace_append hprefix tailTrace_3091510
  have hstable : (prefixWord ++ tailWord_3091510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091510).length < 2 ^ (prefixWord ++ tailWord_3091510).sum := by decide
  have hdescent : baseEnd_3091510 < baseStart_3091510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091538 : List Nat := [3, 2, 2, 1, 3, 1, 4, 6]
def baseStart_3091538 : Nat := 118140960795 + 3091538 * 2 ^ 59
def prefixEnd_3091538 : Nat := 4983230072969 + 3 ^ 40 * 3091538 * 2
def baseEnd_3091538 : Nat := 117588515232565227930169

theorem tailTrace_3091538 : CollatzResearch.WordTrace tailWord_3091538 prefixEnd_3091538 117588515232565227930169 := by
  unfold tailWord_3091538
  simp only [CollatzResearch.WordTrace]
  refine ⟨28189413568473323374966817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75171769515928862333244845 28189413568473323374966817)
  ·
    refine ⟨21142060176354992531225113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28189413568473323374966817 21142060176354992531225113)
    ·
      refine ⟨15856545132266244398418835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21142060176354992531225113 15856545132266244398418835)
      ·
        refine ⟨23784817698399366597628253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15856545132266244398418835 23784817698399366597628253)
        ·
          refine ⟨8919306636899762474110595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23784817698399366597628253 8919306636899762474110595)
          ·
            refine ⟨13378959955349643711165893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8919306636899762474110595 13378959955349643711165893)
            ·
              refine ⟨2508554991628058195843605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13378959955349643711165893 2508554991628058195843605)
              ·
                refine ⟨117588515232565227930169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2508554991628058195843605 117588515232565227930169)
                ·
                  rfl

theorem cell22_3091538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_3091538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091538 prefixEnd_3091538 := by exact prefixLift 3091538
  have htrace : WordTrace (prefixWord ++ tailWord_3091538) baseStart_3091538 baseEnd_3091538 := by
    simpa [prefixWord, tailWord_3091538, baseEnd_3091538] using wordTrace_append hprefix tailTrace_3091538
  have hstable : (prefixWord ++ tailWord_3091538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091538).length < 2 ^ (prefixWord ++ tailWord_3091538).sum := by decide
  have hdescent : baseEnd_3091538 < baseStart_3091538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091581 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3091581 : Nat := 118140960795 + 3091581 * 2 ^ 59
def prefixEnd_3091581 : Nat := 4983230072969 + 3 ^ 40 * 3091581 * 2
def baseEnd_3091581 : Nat := 1058311356871849272546389

theorem tailTrace_3091581 : CollatzResearch.WordTrace tailWord_3091581 prefixEnd_3091581 1058311356871849272546389 := by
  unfold tailWord_3091581
  simp only [CollatzResearch.WordTrace]
  refine ⟨112759222612737511843682597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75172815075158341229121731 112759222612737511843682597)
  ·
    refine ⟨21142354239888283470690487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112759222612737511843682597 21142354239888283470690487)
    ·
      refine ⟨31713531359832425206035731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21142354239888283470690487 31713531359832425206035731)
      ·
        refine ⟨47570297039748637809053597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31713531359832425206035731 47570297039748637809053597)
        ·
          refine ⟨17838861389905739178395099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47570297039748637809053597 17838861389905739178395099)
          ·
            refine ⟨26758292084858608767592649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17838861389905739178395099 26758292084858608767592649)
            ·
              refine ⟨20068719063643956575694487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26758292084858608767592649 20068719063643956575694487)
              ·
                refine ⟨30103078595465934863541731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20068719063643956575694487 30103078595465934863541731)
                ·
                  refine ⟨45154617893198902295312597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30103078595465934863541731 45154617893198902295312597)
                  ·
                    refine ⟨1058311356871849272546389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45154617893198902295312597 1058311356871849272546389)
                    ·
                      rfl

theorem cell22_3091581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3091581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091581 prefixEnd_3091581 := by exact prefixLift 3091581
  have htrace : WordTrace (prefixWord ++ tailWord_3091581) baseStart_3091581 baseEnd_3091581 := by
    simpa [prefixWord, tailWord_3091581, baseEnd_3091581] using wordTrace_append hprefix tailTrace_3091581
  have hstable : (prefixWord ++ tailWord_3091581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091581).length < 2 ^ (prefixWord ++ tailWord_3091581).sum := by decide
  have hdescent : baseEnd_3091581 < baseStart_3091581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091656 : List Nat := [2, 1, 3, 1, 2, 1, 2, 10]
def baseStart_3091656 : Nat := 118140960795 + 3091656 * 2 ^ 59
def prefixEnd_3091656 : Nat := 4983230072969 + 3 ^ 40 * 3091656 * 2
def baseEnd_3091656 : Nat := 117593003433841564102351

theorem tailTrace_3091656 : CollatzResearch.WordTrace tailWord_3091656 prefixEnd_3091656 117593003433841564102351 := by
  unfold tailWord_3091656
  simp only [CollatzResearch.WordTrace]
  refine ⟨56380979043732899826331411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75174638724977199768441881 56380979043732899826331411)
  ·
    refine ⟨84571468565599349739497117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56380979043732899826331411 84571468565599349739497117)
    ·
      refine ⟨31714300712099756152311419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84571468565599349739497117 31714300712099756152311419)
      ·
        refine ⟨47571451068149634228467129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31714300712099756152311419 47571451068149634228467129)
        ·
          refine ⟨35678588301112225671350347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47571451068149634228467129 35678588301112225671350347)
          ·
            refine ⟨53517882451668338507025521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35678588301112225671350347 53517882451668338507025521)
            ·
              refine ⟨40138411838751253880269141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53517882451668338507025521 40138411838751253880269141)
              ·
                refine ⟨117593003433841564102351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40138411838751253880269141 117593003433841564102351)
                ·
                  rfl

theorem cell22_3091656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 10].length) (baseStart_3091656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091656 prefixEnd_3091656 := by exact prefixLift 3091656
  have htrace : WordTrace (prefixWord ++ tailWord_3091656) baseStart_3091656 baseEnd_3091656 := by
    simpa [prefixWord, tailWord_3091656, baseEnd_3091656] using wordTrace_append hprefix tailTrace_3091656
  have hstable : (prefixWord ++ tailWord_3091656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091656).length < 2 ^ (prefixWord ++ tailWord_3091656).sum := by decide
  have hdescent : baseEnd_3091656 < baseStart_3091656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091658 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3091658 : Nat := 118140960795 + 3091658 * 2 ^ 59
def prefixEnd_3091658 : Nat := 4983230072969 + 3 ^ 40 * 3091658 * 2
def baseEnd_3091658 : Nat := 1058337715545446738371153

theorem tailTrace_3091658 : CollatzResearch.WordTrace tailWord_3091658 prefixEnd_3091658 1058337715545446738371153 := by
  unfold tailWord_3091658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28190507758364638498558907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75174687355639035996157085 28190507758364638498558907)
  ·
    refine ⟨42285761637546957747838361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28190507758364638498558907 42285761637546957747838361)
    ·
      refine ⟨31714321228160218310878771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42285761637546957747838361 31714321228160218310878771)
      ·
        refine ⟨47571481842240327466318157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31714321228160218310878771 47571481842240327466318157)
        ·
          refine ⟨17839305690840122799869309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47571481842240327466318157 17839305690840122799869309)
          ·
            refine ⟨6689739634065046049950991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17839305690840122799869309 6689739634065046049950991)
            ·
              refine ⟨10034609451097569074926487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689739634065046049950991 10034609451097569074926487)
              ·
                refine ⟨15051914176646353612389731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034609451097569074926487 15051914176646353612389731)
                ·
                  refine ⟨22577871264969530418584597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15051914176646353612389731 22577871264969530418584597)
                  ·
                    refine ⟨1058337715545446738371153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22577871264969530418584597 1058337715545446738371153)
                    ·
                      rfl

theorem cell22_3091658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3091658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091658 prefixEnd_3091658 := by exact prefixLift 3091658
  have htrace : WordTrace (prefixWord ++ tailWord_3091658) baseStart_3091658 baseEnd_3091658 := by
    simpa [prefixWord, tailWord_3091658, baseEnd_3091658] using wordTrace_append hprefix tailTrace_3091658
  have hstable : (prefixWord ++ tailWord_3091658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091658).length < 2 ^ (prefixWord ++ tailWord_3091658).sum := by decide
  have hdescent : baseEnd_3091658 < baseStart_3091658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091662 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 4]
def baseStart_3091662 : Nat := 118140960795 + 3091662 * 2 ^ 59
def prefixEnd_3091662 : Nat := 4983230072969 + 3 ^ 40 * 3091662 * 2
def baseEnd_3091662 : Nat := 352779694942397353757047

theorem tailTrace_3091662 : CollatzResearch.WordTrace tailWord_3091662 prefixEnd_3091662 352779694942397353757047 := by
  unfold tailWord_3091662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14095272115680507834672655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75174784616962708451587493 14095272115680507834672655)
  ·
    refine ⟨21142908173520761752008983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14095272115680507834672655 21142908173520761752008983)
    ·
      refine ⟨31714362260281142628013475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21142908173520761752008983 31714362260281142628013475)
      ·
        refine ⟨47571543390421713942020213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31714362260281142628013475 47571543390421713942020213)
        ·
          refine ⟨4459832192852035682064395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47571543390421713942020213 4459832192852035682064395)
          ·
            refine ⟨6689748289278053523096593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459832192852035682064395 6689748289278053523096593)
            ·
              refine ⟨5017311216958540142322445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6689748289278053523096593 5017311216958540142322445)
              ·
                refine ⟨1881491706359452553370917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5017311216958540142322445 1881491706359452553370917)
                ·
                  refine ⟨352779694942397353757047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881491706359452553370917 352779694942397353757047)
                  ·
                    rfl

theorem cell22_3091662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_3091662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091662 prefixEnd_3091662 := by exact prefixLift 3091662
  have htrace : WordTrace (prefixWord ++ tailWord_3091662) baseStart_3091662 baseEnd_3091662 := by
    simpa [prefixWord, tailWord_3091662, baseEnd_3091662] using wordTrace_append hprefix tailTrace_3091662
  have hstable : (prefixWord ++ tailWord_3091662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091662).length < 2 ^ (prefixWord ++ tailWord_3091662).sum := by decide
  have hdescent : baseEnd_3091662 < baseStart_3091662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091677 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3091677 : Nat := 118140960795 + 3091677 * 2 ^ 59
def prefixEnd_3091677 : Nat := 4983230072969 + 3 ^ 40 * 3091677 * 2
def baseEnd_3091677 : Nat := 1058344219633737022146095

theorem tailTrace_3091677 : CollatzResearch.WordTrace tailWord_3091677 prefixEnd_3091677 1058344219633737022146095 := by
  unfold tailWord_3091677
  simp only [CollatzResearch.WordTrace]
  refine ⟨112762724020389720239177285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75175149346926480159451523 112762724020389720239177285)
  ·
    refine ⟨21143010753823072544845741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112762724020389720239177285 21143010753823072544845741)
    ·
      refine ⟨7928629032683652204317153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21143010753823072544845741 7928629032683652204317153)
      ·
        refine ⟨5946471774512739153237865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7928629032683652204317153 5946471774512739153237865)
        ·
          refine ⟨4459853830884554364928399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5946471774512739153237865 4459853830884554364928399)
          ·
            refine ⟨6689780746326831547392599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4459853830884554364928399 6689780746326831547392599)
            ·
              refine ⟨10034671119490247321088899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689780746326831547392599 10034671119490247321088899)
              ·
                refine ⟨15052006679235370981633349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034671119490247321088899 15052006679235370981633349)
                ·
                  refine ⟨2822251252356632059056253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15052006679235370981633349 2822251252356632059056253)
                  ·
                    refine ⟨1058344219633737022146095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822251252356632059056253 1058344219633737022146095)
                    ·
                      rfl

theorem cell22_3091677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3091677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091677 prefixEnd_3091677 := by exact prefixLift 3091677
  have htrace : WordTrace (prefixWord ++ tailWord_3091677) baseStart_3091677 baseEnd_3091677 := by
    simpa [prefixWord, tailWord_3091677, baseEnd_3091677] using wordTrace_append hprefix tailTrace_3091677
  have hstable : (prefixWord ++ tailWord_3091677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091677).length < 2 ^ (prefixWord ++ tailWord_3091677).sum := by decide
  have hdescent : baseEnd_3091677 < baseStart_3091677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091752 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 5]
def baseStart_3091752 : Nat := 118140960795 + 3091752 * 2 ^ 59
def prefixEnd_3091752 : Nat := 4983230072969 + 3 ^ 40 * 3091752 * 2
def baseEnd_3091752 : Nat := 352789964555487275506955

theorem tailTrace_3091752 : CollatzResearch.WordTrace tailWord_3091752 prefixEnd_3091752 352789964555487275506955 := by
  unfold tailWord_3091752
  simp only [CollatzResearch.WordTrace]
  refine ⟨56382729747559004024078755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75176972996745338698771673 56382729747559004024078755)
  ·
    refine ⟨84574094621338506036118133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56382729747559004024078755 84574094621338506036118133)
    ·
      refine ⟨7928821370750484940886075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84574094621338506036118133 7928821370750484940886075)
      ·
        refine ⟨11893232056125727411329113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7928821370750484940886075 11893232056125727411329113)
        ·
          refine ⟨8919924042094295558496835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11893232056125727411329113 8919924042094295558496835)
          ·
            refine ⟨13379886063141443337745253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8919924042094295558496835 13379886063141443337745253)
            ·
              refine ⟨2508728636839020625827235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13379886063141443337745253 2508728636839020625827235)
              ·
                refine ⟨3763092955258530938740853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2508728636839020625827235 3763092955258530938740853)
                ·
                  refine ⟨352789964555487275506955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3763092955258530938740853 352789964555487275506955)
                  ·
                    rfl

theorem cell22_3091752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_3091752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091752 prefixEnd_3091752 := by exact prefixLift 3091752
  have htrace : WordTrace (prefixWord ++ tailWord_3091752) baseStart_3091752 baseEnd_3091752 := by
    simpa [prefixWord, tailWord_3091752, baseEnd_3091752] using wordTrace_append hprefix tailTrace_3091752
  have hstable : (prefixWord ++ tailWord_3091752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091752).length < 2 ^ (prefixWord ++ tailWord_3091752).sum := by decide
  have hdescent : baseEnd_3091752 < baseStart_3091752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091765 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 3, 4]
def baseStart_3091765 : Nat := 118140960795 + 3091765 * 2 ^ 59
def prefixEnd_3091765 : Nat := 4983230072969 + 3 ^ 40 * 3091765 * 2
def baseEnd_3091765 : Nat := 1058374343832134125945825

theorem tailTrace_3091765 : CollatzResearch.WordTrace tailWord_3091765 prefixEnd_3091765 1058374343832134125945825 := by
  unfold tailWord_3091765
  simp only [CollatzResearch.WordTrace]
  refine ⟨112765933644070911268380749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75177289096047274178920499 112765933644070911268380749)
  ·
    refine ⟨42287225116526591725642781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112765933644070911268380749 42287225116526591725642781)
    ·
      refine ⟨15857709418697471897116043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42287225116526591725642781 15857709418697471897116043)
      ·
        refine ⟨23786564128046207845674065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15857709418697471897116043 23786564128046207845674065)
        ·
          refine ⟨17839923096034655884255549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23786564128046207845674065 17839923096034655884255549)
          ·
            refine ⟨6689971161012995956595831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17839923096034655884255549 6689971161012995956595831)
            ·
              refine ⟨10034956741519493934893747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6689971161012995956595831 10034956741519493934893747)
              ·
                refine ⟨15052435112279240902340621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10034956741519493934893747 15052435112279240902340621)
                ·
                  refine ⟨5644663167104715338377733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15052435112279240902340621 5644663167104715338377733)
                  ·
                    refine ⟨1058374343832134125945825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5644663167104715338377733 1058374343832134125945825)
                    ·
                      rfl

theorem cell22_3091765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_3091765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091765 prefixEnd_3091765 := by exact prefixLift 3091765
  have htrace : WordTrace (prefixWord ++ tailWord_3091765) baseStart_3091765 baseEnd_3091765 := by
    simpa [prefixWord, tailWord_3091765, baseEnd_3091765] using wordTrace_append hprefix tailTrace_3091765
  have hstable : (prefixWord ++ tailWord_3091765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091765).length < 2 ^ (prefixWord ++ tailWord_3091765).sum := by decide
  have hdescent : baseEnd_3091765 < baseStart_3091765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091797 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 4]
def baseStart_3091797 : Nat := 118140960795 + 3091797 * 2 ^ 59
def prefixEnd_3091797 : Nat := 4983230072969 + 3 ^ 40 * 3091797 * 2
def baseEnd_3091797 : Nat := 352795099362032236381909

theorem tailTrace_3091797 : CollatzResearch.WordTrace tailWord_3091797 prefixEnd_3091797 352795099362032236381909 := by
  unfold tailWord_3091797
  simp only [CollatzResearch.WordTrace]
  refine ⟨112767100779954980733545645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75178067186636653822363763 112767100779954980733545645)
  ·
    refine ⟨42287662792483117775079617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112767100779954980733545645 42287662792483117775079617)
    ·
      refine ⟨31715747094362338331309713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42287662792483117775079617 31715747094362338331309713)
      ·
        refine ⟨23786810320771753748482285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31715747094362338331309713 23786810320771753748482285)
        ·
          refine ⟨8920053870289407655680857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23786810320771753748482285 8920053870289407655680857)
          ·
            refine ⟨6690040402717055741760643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8920053870289407655680857 6690040402717055741760643)
            ·
              refine ⟨10035060604075583612640965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690040402717055741760643 10035060604075583612640965)
              ·
                refine ⟨1881573863264171927370181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10035060604075583612640965 1881573863264171927370181)
                ·
                  refine ⟨352795099362032236381909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881573863264171927370181 352795099362032236381909)
                  ·
                    rfl

theorem cell22_3091797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_3091797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091797 prefixEnd_3091797 := by exact prefixLift 3091797
  have htrace : WordTrace (prefixWord ++ tailWord_3091797) baseStart_3091797 baseEnd_3091797 := by
    simpa [prefixWord, tailWord_3091797, baseEnd_3091797] using wordTrace_append hprefix tailTrace_3091797
  have hstable : (prefixWord ++ tailWord_3091797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091797).length < 2 ^ (prefixWord ++ tailWord_3091797).sum := by decide
  have hdescent : baseEnd_3091797 < baseStart_3091797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091810 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3091810 : Nat := 118140960795 + 3091810 * 2 ^ 59
def prefixEnd_3091810 : Nat := 4983230072969 + 3 ^ 40 * 3091810 * 2
def baseEnd_3091810 : Nat := 1058389748251769008570687

theorem tailTrace_3091810 : CollatzResearch.WordTrace tailWord_3091810 prefixEnd_3091810 1058389748251769008570687 := by
  unfold tailWord_3091810
  simp only [CollatzResearch.WordTrace]
  refine ⟨28191893732226970988442221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75178383285938589302512589 28191893732226970988442221)
  ·
    refine ⟨10571960149585114120665833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28191893732226970988442221 10571960149585114120665833)
    ·
      refine ⟨7928970112188835590499375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10571960149585114120665833 7928970112188835590499375)
      ·
        refine ⟨11893455168283253385749063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7928970112188835590499375 11893455168283253385749063)
        ·
          refine ⟨17840182752424880078623595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11893455168283253385749063 17840182752424880078623595)
          ·
            refine ⟨26760274128637320117935393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17840182752424880078623595 26760274128637320117935393)
            ·
              refine ⟨20070205596477990088451545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26760274128637320117935393 20070205596477990088451545)
              ·
                refine ⟨15052654197358492566338659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20070205596477990088451545 15052654197358492566338659)
                ·
                  refine ⟨22578981296037738849507989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15052654197358492566338659 22578981296037738849507989)
                  ·
                    refine ⟨1058389748251769008570687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22578981296037738849507989 1058389748251769008570687)
                    ·
                      rfl

theorem cell22_3091810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3091810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091810 prefixEnd_3091810 := by exact prefixLift 3091810
  have htrace : WordTrace (prefixWord ++ tailWord_3091810) baseStart_3091810 baseEnd_3091810 := by
    simpa [prefixWord, tailWord_3091810, baseEnd_3091810] using wordTrace_append hprefix tailTrace_3091810
  have hstable : (prefixWord ++ tailWord_3091810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091810).length < 2 ^ (prefixWord ++ tailWord_3091810).sum := by decide
  have hdescent : baseEnd_3091810 < baseStart_3091810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091812 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_3091812 : Nat := 118140960795 + 3091812 * 2 ^ 59
def prefixEnd_3091812 : Nat := 4983230072969 + 3 ^ 40 * 3091812 * 2
def baseEnd_3091812 : Nat := 1058390432892641670020681

theorem tailTrace_3091812 : CollatzResearch.WordTrace tailWord_3091812 prefixEnd_3091812 1058390432892641670020681 := by
  unfold tailWord_3091812
  simp only [CollatzResearch.WordTrace]
  refine ⟨56383823937450319147670845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75178431916600425530227793 56383823937450319147670845)
  ·
    refine ⟨21143933976543869680376567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56383823937450319147670845 21143933976543869680376567)
    ·
      refine ⟨31715900964815804520564851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21143933976543869680376567 31715900964815804520564851)
      ·
        refine ⟨47573851447223706780847277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31715900964815804520564851 47573851447223706780847277)
        ·
          refine ⟨17840194292708890042817729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47573851447223706780847277 17840194292708890042817729)
          ·
            refine ⟨13380145719531667532113297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17840194292708890042817729 13380145719531667532113297)
            ·
              refine ⟨10035109289648750649084973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13380145719531667532113297 10035109289648750649084973)
              ·
                refine ⟨3763165983618281493406865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10035109289648750649084973 3763165983618281493406865)
                ·
                  refine ⟨2822374487713711120055149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3763165983618281493406865 2822374487713711120055149)
                  ·
                    refine ⟨1058390432892641670020681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822374487713711120055149 1058390432892641670020681)
                    ·
                      rfl

theorem cell22_3091812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_3091812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091812 prefixEnd_3091812 := by exact prefixLift 3091812
  have htrace : WordTrace (prefixWord ++ tailWord_3091812) baseStart_3091812 baseEnd_3091812 := by
    simpa [prefixWord, tailWord_3091812, baseEnd_3091812] using wordTrace_append hprefix tailTrace_3091812
  have hstable : (prefixWord ++ tailWord_3091812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091812).length < 2 ^ (prefixWord ++ tailWord_3091812).sum := by decide
  have hdescent : baseEnd_3091812 < baseStart_3091812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091842 : List Nat := [3, 4, 2, 1, 1, 2, 9]
def baseStart_3091842 : Nat := 118140960795 + 3091842 * 2 ^ 59
def prefixEnd_3091842 : Nat := 4983230072969 + 3 ^ 40 * 3091842 * 2
def baseEnd_3091842 : Nat := 39200026018730799695207

theorem tailTrace_3091842 : CollatzResearch.WordTrace tailWord_3091842 prefixEnd_3091842 39200026018730799695207 := by
  unfold tailWord_3091842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28192185516197988354733445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75179161376527968945955853 28192185516197988354733445)
  ·
    refine ⟨5286034784287122816512521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28192185516197988354733445 5286034784287122816512521)
    ·
      refine ⟨3964526088215342112384391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5286034784287122816512521 3964526088215342112384391)
      ·
        refine ⟨5946789132323013168576587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3964526088215342112384391 5946789132323013168576587)
        ·
          refine ⟨8920183698484519752864881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946789132323013168576587 8920183698484519752864881)
          ·
            refine ⟨6690137773863389814648661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8920183698484519752864881 6690137773863389814648661)
            ·
              refine ⟨39200026018730799695207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6690137773863389814648661 39200026018730799695207)
              ·
                rfl

theorem cell22_3091842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 9].length) (baseStart_3091842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091842 prefixEnd_3091842 := by exact prefixLift 3091842
  have htrace : WordTrace (prefixWord ++ tailWord_3091842) baseStart_3091842 baseEnd_3091842 := by
    simpa [prefixWord, tailWord_3091842, baseEnd_3091842] using wordTrace_append hprefix tailTrace_3091842
  have hstable : (prefixWord ++ tailWord_3091842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091842).length < 2 ^ (prefixWord ++ tailWord_3091842).sum := by decide
  have hdescent : baseEnd_3091842 < baseStart_3091842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091908 : List Nat := [2, 3, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_3091908 : Nat := 118140960795 + 3091908 * 2 ^ 59
def prefixEnd_3091908 : Nat := 4983230072969 + 3 ^ 40 * 3091908 * 2
def baseEnd_3091908 : Nat := 1058423295654529419620387

theorem tailTrace_3091908 : CollatzResearch.WordTrace tailWord_3091908 prefixEnd_3091908 1058423295654529419620387 := by
  unfold tailWord_3091908
  simp only [CollatzResearch.WordTrace]
  refine ⟨56385574641276423345418189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75180766188368564460557585 56385574641276423345418189)
  ·
    refine ⟨21144590490478658754531821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56385574641276423345418189 21144590490478658754531821)
    ·
      refine ⟨7929221433929497032949433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21144590490478658754531821 7929221433929497032949433)
      ·
        refine ⟨5946916075447122774712075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7929221433929497032949433 5946916075447122774712075)
        ·
          refine ⟨8920374113170684162068113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5946916075447122774712075 8920374113170684162068113)
          ·
            refine ⟨6690280584878013121551085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8920374113170684162068113 6690280584878013121551085)
            ·
              refine ⟨2508855219329254920581657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6690280584878013121551085 2508855219329254920581657)
              ·
                refine ⟨1881641414496941190436243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2508855219329254920581657 1881641414496941190436243)
                ·
                  refine ⟨2822462121745411785654365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881641414496941190436243 2822462121745411785654365)
                  ·
                    refine ⟨1058423295654529419620387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822462121745411785654365 1058423295654529419620387)
                    ·
                      rfl

theorem cell22_3091908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_3091908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091908 prefixEnd_3091908 := by exact prefixLift 3091908
  have htrace : WordTrace (prefixWord ++ tailWord_3091908) baseStart_3091908 baseEnd_3091908 := by
    simpa [prefixWord, tailWord_3091908, baseEnd_3091908] using wordTrace_append hprefix tailTrace_3091908
  have hstable : (prefixWord ++ tailWord_3091908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091908).length < 2 ^ (prefixWord ++ tailWord_3091908).sum := by decide
  have hdescent : baseEnd_3091908 < baseStart_3091908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3091915 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 6]
def baseStart_3091915 : Nat := 118140960795 + 3091915 * 2 ^ 59
def prefixEnd_3091915 : Nat := 4983230072969 + 3 ^ 40 * 3091915 * 2
def baseEnd_3091915 : Nat := 352808563965861244898455

theorem tailTrace_3091915 : CollatzResearch.WordTrace tailWord_3091915 prefixEnd_3091915 352808563965861244898455 := by
  unfold tailWord_3091915
  simp only [CollatzResearch.WordTrace]
  refine ⟨112771404593527486886341199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75180936395684991257560799 112771404593527486886341199)
  ·
    refine ⟨169157106890291230329511799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112771404593527486886341199 169157106890291230329511799)
    ·
      refine ⟨253735660335436845494267699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169157106890291230329511799 253735660335436845494267699)
      ·
        refine ⟨380603490503155268241401549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253735660335436845494267699 380603490503155268241401549)
        ·
          refine ⟨142726308938683225590525581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380603490503155268241401549 142726308938683225590525581)
          ·
            refine ⟨53522365852006209596447093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 142726308938683225590525581 53522365852006209596447093)
            ·
              refine ⟨5017721798625582149666915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53522365852006209596447093 5017721798625582149666915)
              ·
                refine ⟨7526582697938373224500373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5017721798625582149666915 7526582697938373224500373)
                ·
                  refine ⟨352808563965861244898455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7526582697938373224500373 352808563965861244898455)
                  ·
                    rfl

theorem cell22_3091915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 6].length) (baseStart_3091915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3091915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3091915 prefixEnd_3091915 := by exact prefixLift 3091915
  have htrace : WordTrace (prefixWord ++ tailWord_3091915) baseStart_3091915 baseEnd_3091915 := by
    simpa [prefixWord, tailWord_3091915, baseEnd_3091915] using wordTrace_append hprefix tailTrace_3091915
  have hstable : (prefixWord ++ tailWord_3091915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3091915).length < 2 ^ (prefixWord ++ tailWord_3091915).sum := by decide
  have hdescent : baseEnd_3091915 < baseStart_3091915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3091915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092005 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 7]
def baseStart_3092005 : Nat := 118140960795 + 3092005 * 2 ^ 59
def prefixEnd_3092005 : Nat := 4983230072969 + 3 ^ 40 * 3092005 * 2
def baseEnd_3092005 : Nat := 352818833578951166648363

theorem tailTrace_3092005 : CollatzResearch.WordTrace tailWord_3092005 prefixEnd_3092005 352818833578951166648363 := by
  unfold tailWord_3092005
  simp only [CollatzResearch.WordTrace]
  refine ⟨112774687163201432257117469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75183124775467621504744979 112774687163201432257117469)
  ·
    refine ⟨42290507686200537096419051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112774687163201432257117469 42290507686200537096419051)
    ·
      refine ⟨63435761529300805644628577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42290507686200537096419051 63435761529300805644628577)
      ·
        refine ⟨47576821146975604233471433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63435761529300805644628577 47576821146975604233471433)
        ·
          refine ⟨35682615860231703175103575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47576821146975604233471433 35682615860231703175103575)
          ·
            refine ⟨53523923790347554762655363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35682615860231703175103575 53523923790347554762655363)
            ·
              refine ⟨80285885685521332143983045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53523923790347554762655363 80285885685521332143983045)
              ·
                refine ⟨15053603566035249776996821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80285885685521332143983045 15053603566035249776996821)
                ·
                  refine ⟨352818833578951166648363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15053603566035249776996821 352818833578951166648363)
                  ·
                    rfl

theorem cell22_3092005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 7].length) (baseStart_3092005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092005 prefixEnd_3092005 := by exact prefixLift 3092005
  have htrace : WordTrace (prefixWord ++ tailWord_3092005) baseStart_3092005 baseEnd_3092005 := by
    simpa [prefixWord, tailWord_3092005, baseEnd_3092005] using wordTrace_append hprefix tailTrace_3092005
  have hstable : (prefixWord ++ tailWord_3092005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092005).length < 2 ^ (prefixWord ++ tailWord_3092005).sum := by decide
  have hdescent : baseEnd_3092005 < baseStart_3092005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092069 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_3092069 : Nat := 118140960795 + 3092069 * 2 ^ 59
def prefixEnd_3092069 : Nat := 4983230072969 + 3 ^ 40 * 3092069 * 2
def baseEnd_3092069 : Nat := 1058478409244778666344893

theorem tailTrace_3092069 : CollatzResearch.WordTrace tailWord_3092069 prefixEnd_3092069 1058478409244778666344893 := by
  unfold tailWord_3092069
  simp only [CollatzResearch.WordTrace]
  refine ⟨112777021434969571187447261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75184680956646380791631507 112777021434969571187447261)
  ·
    refine ⟨42291383038113589195292723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112777021434969571187447261 42291383038113589195292723)
    ·
      refine ⟨63437074557170383792939085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42291383038113589195292723 63437074557170383792939085)
      ·
        refine ⟨23788902958938893922352157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63437074557170383792939085 23788902958938893922352157)
        ·
          refine ⟨8920838609602085220882059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23788902958938893922352157 8920838609602085220882059)
          ·
            refine ⟨13381257914403127831323089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8920838609602085220882059 13381257914403127831323089)
            ·
              refine ⟨10035943435802345873492317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13381257914403127831323089 10035943435802345873492317)
              ·
                refine ⟨3763478788425879702559619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10035943435802345873492317 3763478788425879702559619)
                ·
                  refine ⟨5645218182638819553839429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3763478788425879702559619 5645218182638819553839429)
                  ·
                    refine ⟨1058478409244778666344893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5645218182638819553839429 1058478409244778666344893)
                    ·
                      rfl

theorem cell22_3092069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_3092069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092069 prefixEnd_3092069 := by exact prefixLift 3092069
  have htrace : WordTrace (prefixWord ++ tailWord_3092069) baseStart_3092069 baseEnd_3092069 := by
    simpa [prefixWord, tailWord_3092069, baseEnd_3092069] using wordTrace_append hprefix tailTrace_3092069
  have hstable : (prefixWord ++ tailWord_3092069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092069).length < 2 ^ (prefixWord ++ tailWord_3092069).sum := by decide
  have hdescent : baseEnd_3092069 < baseStart_3092069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092116 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_3092116 : Nat := 118140960795 + 3092116 * 2 ^ 59
def prefixEnd_3092116 : Nat := 4983230072969 + 3 ^ 40 * 3092116 * 2
def baseEnd_3092116 : Nat := 1058494498305286210419749

theorem tailTrace_3092116 : CollatzResearch.WordTrace tailWord_3092116 prefixEnd_3092116 1058494498305286210419749 := by
  unfold tailWord_3092116
  simp only [CollatzResearch.WordTrace]
  refine ⟨56389367832899649107204101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75185823777199532142938801 56389367832899649107204101)
  ·
    refine ⟨10573006468668684207600769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56389367832899649107204101 10573006468668684207600769)
    ·
      refine ⟨7929754851501513155700577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10573006468668684207600769 7929754851501513155700577)
      ·
        refine ⟨5947316138626134866775433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7929754851501513155700577 5947316138626134866775433)
        ·
          refine ⟨4460487103969601150081575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5947316138626134866775433 4460487103969601150081575)
          ·
            refine ⟨6690730655954401725122363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460487103969601150081575 6690730655954401725122363)
            ·
              refine ⟨10036095983931602587683545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6690730655954401725122363 10036095983931602587683545)
              ·
                refine ⟨7527071987948701940762659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036095983931602587683545 7527071987948701940762659)
                ·
                  refine ⟨11290607981923052911143989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7527071987948701940762659 11290607981923052911143989)
                  ·
                    refine ⟨1058494498305286210419749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11290607981923052911143989 1058494498305286210419749)
                    ·
                      rfl

theorem cell22_3092116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_3092116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092116 prefixEnd_3092116 := by exact prefixLift 3092116
  have htrace : WordTrace (prefixWord ++ tailWord_3092116) baseStart_3092116 baseEnd_3092116 := by
    simpa [prefixWord, tailWord_3092116, baseEnd_3092116] using wordTrace_append hprefix tailTrace_3092116
  have hstable : (prefixWord ++ tailWord_3092116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092116).length < 2 ^ (prefixWord ++ tailWord_3092116).sum := by decide
  have hdescent : baseEnd_3092116 < baseStart_3092116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092178 : List Nat := [3, 2, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_3092178 : Nat := 118140960795 + 3092178 * 2 ^ 59
def prefixEnd_3092178 : Nat := 4983230072969 + 3 ^ 40 * 3092178 * 2
def baseEnd_3092178 : Nat := 1058515722172338715369559

theorem tailTrace_3092178 : CollatzResearch.WordTrace tailWord_3092178 prefixEnd_3092178 1058515722172338715369559 := by
  unfold tailWord_3092178
  simp only [CollatzResearch.WordTrace]
  refine ⟨28195249247893670700791297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75187331327716455202110125 28195249247893670700791297)
  ·
    refine ⟨21146436935920253025593473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28195249247893670700791297 21146436935920253025593473)
    ·
      refine ⟨15859827701940189769195105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21146436935920253025593473 15859827701940189769195105)
      ·
        refine ⟨11894870776455142326896329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15859827701940189769195105 11894870776455142326896329)
        ·
          refine ⟨8921153082341356745172247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11894870776455142326896329 8921153082341356745172247)
          ·
            refine ⟨13381729623512035117758371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8921153082341356745172247 13381729623512035117758371)
            ·
              refine ⟨20072594435268052676637557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13381729623512035117758371 20072594435268052676637557)
              ·
                refine ⟨1881805728306379938434771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20072594435268052676637557 1881805728306379938434771)
                ·
                  refine ⟨2822708592459569907652157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881805728306379938434771 2822708592459569907652157)
                  ·
                    refine ⟨1058515722172338715369559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822708592459569907652157 1058515722172338715369559)
                    ·
                      rfl

theorem cell22_3092178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_3092178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092178 prefixEnd_3092178 := by exact prefixLift 3092178
  have htrace : WordTrace (prefixWord ++ tailWord_3092178) baseStart_3092178 baseEnd_3092178 := by
    simpa [prefixWord, tailWord_3092178, baseEnd_3092178] using wordTrace_append hprefix tailTrace_3092178
  have hstable : (prefixWord ++ tailWord_3092178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092178).length < 2 ^ (prefixWord ++ tailWord_3092178).sum := by decide
  have hdescent : baseEnd_3092178 < baseStart_3092178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092236 : List Nat := [2, 2, 1, 2, 2, 1, 5, 3, 4]
def baseStart_3092236 : Nat := 118140960795 + 3092236 * 2 ^ 59
def prefixEnd_3092236 : Nat := 4983230072969 + 3 ^ 40 * 3092236 * 2
def baseEnd_3092236 : Nat := 352845192252548632473127

theorem tailTrace_3092236 : CollatzResearch.WordTrace tailWord_3092236 prefixEnd_3092236 352845192252548632473127 := by
  unfold tailWord_3092236
  simp only [CollatzResearch.WordTrace]
  refine ⟨56391556212682279354388281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75188741616909705805851041 56391556212682279354388281)
  ·
    refine ⟨42293667159511709515791211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56391556212682279354388281 42293667159511709515791211)
    ·
      refine ⟨63440500739267564273686817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42293667159511709515791211 63440500739267564273686817)
      ·
        refine ⟨47580375554450673205265113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63440500739267564273686817 47580375554450673205265113)
        ·
          refine ⟨35685281665838004903948835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47580375554450673205265113 35685281665838004903948835)
          ·
            refine ⟨53527922498757007355923253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35685281665838004903948835 53527922498757007355923253)
            ·
              refine ⟨5018242734258469439617805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53527922498757007355923253 5018242734258469439617805)
              ·
                refine ⟨1881841025346926039856677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5018242734258469439617805 1881841025346926039856677)
                ·
                  refine ⟨352845192252548632473127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881841025346926039856677 352845192252548632473127)
                  ·
                    rfl

theorem cell22_3092236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_3092236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092236 prefixEnd_3092236 := by exact prefixLift 3092236
  have htrace : WordTrace (prefixWord ++ tailWord_3092236) baseStart_3092236 baseEnd_3092236 := by
    simpa [prefixWord, tailWord_3092236, baseEnd_3092236] using wordTrace_append hprefix tailTrace_3092236
  have hstable : (prefixWord ++ tailWord_3092236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092236).length < 2 ^ (prefixWord ++ tailWord_3092236).sum := by decide
  have hdescent : baseEnd_3092236 < baseStart_3092236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092264 : List Nat := [2, 1, 5, 1, 1, 2, 1, 9]
def baseStart_3092264 : Nat := 118140960795 + 3092264 * 2 ^ 59
def prefixEnd_3092264 : Nat := 4983230072969 + 3 ^ 40 * 3092264 * 2
def baseEnd_3092264 : Nat := 117616129081095906413255

theorem tailTrace_3092264 : CollatzResearch.WordTrace tailWord_3092264 prefixEnd_3092264 117616129081095906413255 := by
  unfold tailWord_3092264
  simp only [CollatzResearch.WordTrace]
  refine ⟨56392066834631559745397923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75189422446175412993863897 56392066834631559745397923)
  ·
    refine ⟨84588100251947339618096885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56392066834631559745397923 84588100251947339618096885)
    ·
      refine ⟨7930134398620063089196583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84588100251947339618096885 7930134398620063089196583)
      ·
        refine ⟨11895201597930094633794875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7930134398620063089196583 11895201597930094633794875)
        ·
          refine ⟨17842802396895141950692313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11895201597930094633794875 17842802396895141950692313)
          ·
            refine ⟨13382101797671356463019235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17842802396895141950692313 13382101797671356463019235)
            ·
              refine ⟨20073152696507034694528853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13382101797671356463019235 20073152696507034694528853)
              ·
                refine ⟨117616129081095906413255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20073152696507034694528853 117616129081095906413255)
                ·
                  rfl

theorem cell22_3092264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_3092264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092264 prefixEnd_3092264 := by exact prefixLift 3092264
  have htrace : WordTrace (prefixWord ++ tailWord_3092264) baseStart_3092264 baseEnd_3092264 := by
    simpa [prefixWord, tailWord_3092264, baseEnd_3092264] using wordTrace_append hprefix tailTrace_3092264
  have hstable : (prefixWord ++ tailWord_3092264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092264).length < 2 ^ (prefixWord ++ tailWord_3092264).sum := by decide
  have hdescent : baseEnd_3092264 < baseStart_3092264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092268 : List Nat := [2, 2, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_3092268 : Nat := 118140960795 + 3092268 * 2 ^ 59
def prefixEnd_3092268 : Nat := 4983230072969 + 3 ^ 40 * 3092268 * 2
def baseEnd_3092268 : Nat := 1058546531011608480619283

theorem tailTrace_3092268 : CollatzResearch.WordTrace tailWord_3092268 prefixEnd_3092268 1058546531011608480619283 := by
  unfold tailWord_3092268
  simp only [CollatzResearch.WordTrace]
  refine ⟨56392139780624314086970729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75189519707499085449294305 56392139780624314086970729)
  ·
    refine ⟨42294104835468235565228047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56392139780624314086970729 42294104835468235565228047)
    ·
      refine ⟨63441157253202353347842071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42294104835468235565228047 63441157253202353347842071)
      ·
        refine ⟨95161735879803530021763107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63441157253202353347842071 95161735879803530021763107)
        ·
          refine ⟨142742603819705295032644661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95161735879803530021763107 142742603819705295032644661)
          ·
            refine ⟨13382119108097371409310437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142742603819705295032644661 13382119108097371409310437)
            ·
              refine ⟨2509147332768257139245707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13382119108097371409310437 2509147332768257139245707)
              ·
                refine ⟨3763720999152385708868561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509147332768257139245707 3763720999152385708868561)
                ·
                  refine ⟨2822790749364289281651421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3763720999152385708868561 2822790749364289281651421)
                  ·
                    refine ⟨1058546531011608480619283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822790749364289281651421 1058546531011608480619283)
                    ·
                      rfl

theorem cell22_3092268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_3092268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092268 prefixEnd_3092268 := by exact prefixLift 3092268
  have htrace : WordTrace (prefixWord ++ tailWord_3092268) baseStart_3092268 baseEnd_3092268 := by
    simpa [prefixWord, tailWord_3092268, baseEnd_3092268] using wordTrace_append hprefix tailTrace_3092268
  have hstable : (prefixWord ++ tailWord_3092268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092268).length < 2 ^ (prefixWord ++ tailWord_3092268).sum := by decide
  have hdescent : baseEnd_3092268 < baseStart_3092268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092313 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 1, 3]
def baseStart_3092313 : Nat := 118140960795 + 3092313 * 2 ^ 59
def prefixEnd_3092313 : Nat := 4983230072969 + 3 ^ 40 * 3092313 * 2
def baseEnd_3092313 : Nat := 1058561935431243363244145

theorem tailTrace_3092313 : CollatzResearch.WordTrace tailWord_3092313 prefixEnd_3092313 1058561935431243363244145 := by
  unfold tailWord_3092313
  simp only [CollatzResearch.WordTrace]
  refine ⟨112785920846085600859329593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75190613897390400572886395 112785920846085600859329593)
  ·
    refine ⟨84589440634564200644497195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112785920846085600859329593 84589440634564200644497195)
    ·
      refine ⟨126884160951846300966745793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84589440634564200644497195 126884160951846300966745793)
      ·
        refine ⟨95163120713884725725059345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126884160951846300966745793 95163120713884725725059345)
        ·
          refine ⟨71372340535413544293794509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95163120713884725725059345 71372340535413544293794509)
          ·
            refine ⟨26764627700780079110172941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71372340535413544293794509 26764627700780079110172941)
            ·
              refine ⟨10036735387792529666314853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26764627700780079110172941 10036735387792529666314853)
              ·
                refine ⟨1881887885211099312434035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10036735387792529666314853 1881887885211099312434035)
                ·
                  refine ⟨2822831827816648968651053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881887885211099312434035 2822831827816648968651053)
                  ·
                    refine ⟨1058561935431243363244145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822831827816648968651053 1058561935431243363244145)
                    ·
                      rfl

theorem cell22_3092313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_3092313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092313 prefixEnd_3092313 := by exact prefixLift 3092313
  have htrace : WordTrace (prefixWord ++ tailWord_3092313) baseStart_3092313 baseEnd_3092313 := by
    simpa [prefixWord, tailWord_3092313, baseEnd_3092313] using wordTrace_append hprefix tailTrace_3092313
  have hstable : (prefixWord ++ tailWord_3092313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092313).length < 2 ^ (prefixWord ++ tailWord_3092313).sum := by decide
  have hdescent : baseEnd_3092313 < baseStart_3092313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092330 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3092330 : Nat := 118140960795 + 3092330 * 2 ^ 59
def prefixEnd_3092330 : Nat := 4983230072969 + 3 ^ 40 * 3092330 * 2
def baseEnd_3092330 : Nat := 1058567754878660985569093

theorem tailTrace_3092330 : CollatzResearch.WordTrace tailWord_3092330 prefixEnd_3092330 1058567754878660985569093 := by
  unfold tailWord_3092330
  simp only [CollatzResearch.WordTrace]
  refine ⟨28196635221756003190674611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75191027258016008508465629 28196635221756003190674611)
  ·
    refine ⟨42294952832634004786011917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28196635221756003190674611 42294952832634004786011917)
    ·
      refine ⟨15860607312237751794754469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42294952832634004786011917 15860607312237751794754469)
      ·
        refine ⟨2973863871044578461516463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15860607312237751794754469 2973863871044578461516463)
        ·
          refine ⟨4460795806566867692274695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2973863871044578461516463 4460795806566867692274695)
          ·
            refine ⟨6691193709850301538412043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460795806566867692274695 6691193709850301538412043)
            ·
              refine ⟨10036790564775452307618065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691193709850301538412043 10036790564775452307618065)
              ·
                refine ⟨7527592923581589230713549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10036790564775452307618065 7527592923581589230713549)
                ·
                  refine ⟨2822847346343095961517581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7527592923581589230713549 2822847346343095961517581)
                  ·
                    refine ⟨1058567754878660985569093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822847346343095961517581 1058567754878660985569093)
                    ·
                      rfl

theorem cell22_3092330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3092330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092330 prefixEnd_3092330 := by exact prefixLift 3092330
  have htrace : WordTrace (prefixWord ++ tailWord_3092330) baseStart_3092330 baseEnd_3092330 := by
    simpa [prefixWord, tailWord_3092330, baseEnd_3092330] using wordTrace_append hprefix tailTrace_3092330
  have hstable : (prefixWord ++ tailWord_3092330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092330).length < 2 ^ (prefixWord ++ tailWord_3092330).sum := by decide
  have hdescent : baseEnd_3092330 < baseStart_3092330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092360 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 5]
def baseStart_3092360 : Nat := 118140960795 + 3092360 * 2 ^ 59
def prefixEnd_3092360 : Nat := 4983230072969 + 3 ^ 40 * 3092360 * 2
def baseEnd_3092360 : Nat := 352859341497250302439667

theorem tailTrace_3092360 : CollatzResearch.WordTrace tailWord_3092360 prefixEnd_3092360 352859341497250302439667 := by
  unfold tailWord_3092360
  simp only [CollatzResearch.WordTrace]
  refine ⟨56393817538457663943145267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75191756717943551924193689 56393817538457663943145267)
  ·
    refine ⟨84590726307686495914717901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56393817538457663943145267 84590726307686495914717901)
    ·
      refine ⟨31721522365382435968019213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84590726307686495914717901 31721522365382435968019213)
      ·
        refine ⟨11895570887018413488007205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31721522365382435968019213 11895570887018413488007205)
        ·
          refine ⟨2230419541315952529001351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11895570887018413488007205 2230419541315952529001351)
          ·
            refine ⟨3345629311973928793502027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230419541315952529001351 3345629311973928793502027)
            ·
              refine ⟨5018443967960893190253041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345629311973928793502027 5018443967960893190253041)
              ·
                refine ⟨3763832975970669892689781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5018443967960893190253041 3763832975970669892689781)
                ·
                  refine ⟨352859341497250302439667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3763832975970669892689781 352859341497250302439667)
                  ·
                    rfl

theorem cell22_3092360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_3092360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092360 prefixEnd_3092360 := by exact prefixLift 3092360
  have htrace : WordTrace (prefixWord ++ tailWord_3092360) baseStart_3092360 baseEnd_3092360 := by
    simpa [prefixWord, tailWord_3092360, baseEnd_3092360] using wordTrace_append hprefix tailTrace_3092360
  have hstable : (prefixWord ++ tailWord_3092360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092360).length < 2 ^ (prefixWord ++ tailWord_3092360).sum := by decide
  have hdescent : baseEnd_3092360 < baseStart_3092360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092369 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_3092369 : Nat := 118140960795 + 3092369 * 2 ^ 59
def prefixEnd_3092369 : Nat := 4983230072969 + 3 ^ 40 * 3092369 * 2
def baseEnd_3092369 : Nat := 1058581105375677883843973

theorem tailTrace_3092369 : CollatzResearch.WordTrace tailWord_3092369 prefixEnd_3092369 1058581105375677883843973 := by
  unfold tailWord_3092369
  simp only [CollatzResearch.WordTrace]
  refine ⟨112787963333882722423368161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75191975555921814948912107 112787963333882722423368161)
  ·
    refine ⟨84590972500412041817526121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112787963333882722423368161 84590972500412041817526121)
    ·
      refine ⟨63443229375309031363144591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84590972500412041817526121 63443229375309031363144591)
      ·
        refine ⟨95164844062963547044716887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63443229375309031363144591 95164844062963547044716887)
        ·
          refine ⟨142747266094445320567075331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95164844062963547044716887 142747266094445320567075331)
          ·
            refine ⟨214120899141667980850612997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142747266094445320567075331 214120899141667980850612997)
            ·
              refine ⟨40147668589062746409489937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214120899141667980850612997 40147668589062746409489937)
              ·
                refine ⟨30110751441797059807117453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40147668589062746409489937 30110751441797059807117453)
                ·
                  refine ⟨11291531790673897427669045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30110751441797059807117453 11291531790673897427669045)
                  ·
                    refine ⟨1058581105375677883843973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11291531790673897427669045 1058581105375677883843973)
                    ·
                      rfl

theorem cell22_3092369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_3092369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092369 prefixEnd_3092369 := by exact prefixLift 3092369
  have htrace : WordTrace (prefixWord ++ tailWord_3092369) baseStart_3092369 baseEnd_3092369 := by
    simpa [prefixWord, tailWord_3092369, baseEnd_3092369] using wordTrace_append hprefix tailTrace_3092369
  have hstable : (prefixWord ++ tailWord_3092369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092369).length < 2 ^ (prefixWord ++ tailWord_3092369).sum := by decide
  have hdescent : baseEnd_3092369 < baseStart_3092369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092398 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3092398 : Nat := 118140960795 + 3092398 * 2 ^ 59
def prefixEnd_3092398 : Nat := 4983230072969 + 3 ^ 40 * 3092398 * 2
def baseEnd_3092398 : Nat := 1058591032668331474868885

theorem tailTrace_3092398 : CollatzResearch.WordTrace tailWord_3092398 prefixEnd_3092398 1058591032668331474868885 := by
  unfold tailWord_3092398
  simp only [CollatzResearch.WordTrace]
  refine ⟨14098627631347207547021731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75192680700518440250782565 14098627631347207547021731)
  ·
    refine ⟨21147941447020811320532597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14098627631347207547021731 21147941447020811320532597)
    ·
      refine ⟨1982619510658201061299931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21147941447020811320532597 1982619510658201061299931)
      ·
        refine ⟨2973929265987301591949897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982619510658201061299931 2973929265987301591949897)
        ·
          refine ⟨2230446949490476193962423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2973929265987301591949897 2230446949490476193962423)
          ·
            refine ⟨3345670424235714290943635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230446949490476193962423 3345670424235714290943635)
            ·
              refine ⟨5018505636353571436415453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345670424235714290943635 5018505636353571436415453)
              ·
                refine ⟨1881939613632589288655795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5018505636353571436415453 1881939613632589288655795)
                ·
                  refine ⟨2822909420448883932983693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1881939613632589288655795 2822909420448883932983693)
                  ·
                    refine ⟨1058591032668331474868885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822909420448883932983693 1058591032668331474868885)
                    ·
                      rfl

theorem cell22_3092398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3092398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092398 prefixEnd_3092398 := by exact prefixLift 3092398
  have htrace : WordTrace (prefixWord ++ tailWord_3092398) baseStart_3092398 baseEnd_3092398 := by
    simpa [prefixWord, tailWord_3092398, baseEnd_3092398] using wordTrace_append hprefix tailTrace_3092398
  have hstable : (prefixWord ++ tailWord_3092398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092398).length < 2 ^ (prefixWord ++ tailWord_3092398).sum := by decide
  have hdescent : baseEnd_3092398 < baseStart_3092398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092399 : List Nat := [1, 1, 2, 1, 2, 2, 5, 8]
def baseStart_3092399 : Nat := 118140960795 + 3092399 * 2 ^ 59
def prefixEnd_3092399 : Nat := 4983230072969 + 3 ^ 40 * 3092399 * 2
def baseEnd_3092399 : Nat := 117621263887640867288209

theorem tailTrace_3092399 : CollatzResearch.WordTrace tailWord_3092399 prefixEnd_3092399 117621263887640867288209 := by
  unfold tailWord_3092399
  simp only [CollatzResearch.WordTrace]
  refine ⟨112789057523774037546960251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75192705015849358364640167 112789057523774037546960251)
  ·
    refine ⟨169183586285661056320440377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112789057523774037546960251 169183586285661056320440377)
    ·
      refine ⟨126887689714245792240330283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169183586285661056320440377 126887689714245792240330283)
      ·
        refine ⟨190331534571368688360495425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126887689714245792240330283 190331534571368688360495425)
        ·
          refine ⟨142748650928526516270371569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190331534571368688360495425 142748650928526516270371569)
          ·
            refine ⟨107061488196394887202778677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142748650928526516270371569 107061488196394887202778677)
            ·
              refine ⟨10037014518412020675260501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107061488196394887202778677 10037014518412020675260501)
              ·
                refine ⟨117621263887640867288209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10037014518412020675260501 117621263887640867288209)
                ·
                  rfl

theorem cell22_3092399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 8].length) (baseStart_3092399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092399 prefixEnd_3092399 := by exact prefixLift 3092399
  have htrace : WordTrace (prefixWord ++ tailWord_3092399) baseStart_3092399 baseEnd_3092399 := by
    simpa [prefixWord, tailWord_3092399, baseEnd_3092399] using wordTrace_append hprefix tailTrace_3092399
  have hstable : (prefixWord ++ tailWord_3092399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092399).length < 2 ^ (prefixWord ++ tailWord_3092399).sum := by decide
  have hdescent : baseEnd_3092399 < baseStart_3092399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092401 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_3092401 : Nat := 118140960795 + 3092401 * 2 ^ 59
def prefixEnd_3092401 : Nat := 4983230072969 + 3 ^ 40 * 3092401 * 2
def baseEnd_3092401 : Nat := 1058592059629640467043875

theorem tailTrace_3092401 : CollatzResearch.WordTrace tailWord_3092401 prefixEnd_3092401 1058592059629640467043875 := by
  unfold tailWord_3092401
  simp only [CollatzResearch.WordTrace]
  refine ⟨112789130469766791888533057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75192753646511194592355371 112789130469766791888533057)
  ·
    refine ⟨84591847852325093916399793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112789130469766791888533057 84591847852325093916399793)
    ·
      refine ⟨63443885889243820437299845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84591847852325093916399793 63443885889243820437299845)
      ·
        refine ⟨11895728604233216331993721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63443885889243820437299845 11895728604233216331993721)
        ·
          refine ⟨8921796453174912248995291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11895728604233216331993721 8921796453174912248995291)
          ·
            refine ⟨13382694679762368373492937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8921796453174912248995291 13382694679762368373492937)
            ·
              refine ⟨10037021009821776280119703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13382694679762368373492937 10037021009821776280119703)
              ·
                refine ⟨15055531514732664420179555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037021009821776280119703 15055531514732664420179555)
                ·
                  refine ⟨22583297272098996630269333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15055531514732664420179555 22583297272098996630269333)
                  ·
                    refine ⟨1058592059629640467043875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22583297272098996630269333 1058592059629640467043875)
                    ·
                      rfl

theorem cell22_3092401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_3092401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092401 prefixEnd_3092401 := by exact prefixLift 3092401
  have htrace : WordTrace (prefixWord ++ tailWord_3092401) baseStart_3092401 baseEnd_3092401 := by
    simpa [prefixWord, tailWord_3092401, baseEnd_3092401] using wordTrace_append hprefix tailTrace_3092401
  have hstable : (prefixWord ++ tailWord_3092401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092401).length < 2 ^ (prefixWord ++ tailWord_3092401).sum := by decide
  have hdescent : baseEnd_3092401 < baseStart_3092401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092405 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 4]
def baseStart_3092405 : Nat := 118140960795 + 3092405 * 2 ^ 59
def prefixEnd_3092405 : Nat := 4983230072969 + 3 ^ 40 * 3092405 * 2
def baseEnd_3092405 : Nat := 352864476303795263314621

theorem tailTrace_3092405 : CollatzResearch.WordTrace tailWord_3092405 prefixEnd_3092405 352864476303795263314621 := by
  unfold tailWord_3092405
  simp only [CollatzResearch.WordTrace]
  refine ⟨112789276361752300571678669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75192850907834867047785779 112789276361752300571678669)
  ·
    refine ⟨42295978635657112714379501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112789276361752300571678669 42295978635657112714379501)
    ·
      refine ⟨15860991988371417267892313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42295978635657112714379501 15860991988371417267892313)
      ·
        refine ⟨11895743991278562950919235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15860991988371417267892313 11895743991278562950919235)
        ·
          refine ⟨17843615986917844426378853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11895743991278562950919235 17843615986917844426378853)
          ·
            refine ⟨3345677997547095829946035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17843615986917844426378853 3345677997547095829946035)
            ·
              refine ⟨5018516996320643744919053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3345677997547095829946035 5018516996320643744919053)
              ·
                refine ⟨1881943873620241404344645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5018516996320643744919053 1881943873620241404344645)
                ·
                  refine ⟨352864476303795263314621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1881943873620241404344645 352864476303795263314621)
                  ·
                    rfl

theorem cell22_3092405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_3092405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092405 prefixEnd_3092405 := by exact prefixLift 3092405
  have htrace : WordTrace (prefixWord ++ tailWord_3092405) baseStart_3092405 baseEnd_3092405 := by
    simpa [prefixWord, tailWord_3092405, baseEnd_3092405] using wordTrace_append hprefix tailTrace_3092405
  have hstable : (prefixWord ++ tailWord_3092405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092405).length < 2 ^ (prefixWord ++ tailWord_3092405).sum := by decide
  have hdescent : baseEnd_3092405 < baseStart_3092405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092437 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 2, 3]
def baseStart_3092437 : Nat := 118140960795 + 3092437 * 2 ^ 59
def prefixEnd_3092437 : Nat := 4983230072969 + 3 ^ 40 * 3092437 * 2
def baseEnd_3092437 : Nat := 1058604383165348373143765

theorem tailTrace_3092437 : CollatzResearch.WordTrace tailWord_3092437 prefixEnd_3092437 1058604383165348373143765 := by
  unfold tailWord_3092437
  simp only [CollatzResearch.WordTrace]
  refine ⟨112790443497636370036843565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75193628998424246691229043 112790443497636370036843565)
  ·
    refine ⟨42296416311613638763816337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112790443497636370036843565 42296416311613638763816337)
    ·
      refine ⟨31722312233710229072862253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42296416311613638763816337 31722312233710229072862253)
      ·
        refine ⟨11895867087641335902323345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31722312233710229072862253 11895867087641335902323345)
        ·
          refine ⟨8921900315731001926742509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11895867087641335902323345 8921900315731001926742509)
          ·
            refine ⟨3345712618399125722528441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8921900315731001926742509 3345712618399125722528441)
            ·
              refine ⟨2509284463799344291896331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3345712618399125722528441 2509284463799344291896331)
              ·
                refine ⟨3763926695699016437844497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509284463799344291896331 3763926695699016437844497)
                ·
                  refine ⟨2822945021774262328383373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3763926695699016437844497 2822945021774262328383373)
                  ·
                    refine ⟨1058604383165348373143765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2822945021774262328383373 1058604383165348373143765)
                    ·
                      rfl

theorem cell22_3092437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 3].length) (baseStart_3092437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092437 prefixEnd_3092437 := by exact prefixLift 3092437
  have htrace : WordTrace (prefixWord ++ tailWord_3092437) baseStart_3092437 baseEnd_3092437 := by
    simpa [prefixWord, tailWord_3092437, baseEnd_3092437] using wordTrace_append hprefix tailTrace_3092437
  have hstable : (prefixWord ++ tailWord_3092437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092437).length < 2 ^ (prefixWord ++ tailWord_3092437).sum := by decide
  have hdescent : baseEnd_3092437 < baseStart_3092437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092476 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_3092476 : Nat := 118140960795 + 3092476 * 2 ^ 59
def prefixEnd_3092476 : Nat := 4983230072969 + 3 ^ 40 * 3092476 * 2
def baseEnd_3092476 : Nat := 1058617733662365271418645

theorem tailTrace_3092476 : CollatzResearch.WordTrace tailWord_3092476 prefixEnd_3092476 1058617733662365271418645 := by
  unfold tailWord_3092476
  simp only [CollatzResearch.WordTrace]
  refine ⟨56395932972247539848756641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75194577296330053131675521 56395932972247539848756641)
  ·
    refine ⟨42296949729185654886567481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56395932972247539848756641 42296949729185654886567481)
    ·
      refine ⟨31722712296889241164925611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42296949729185654886567481 31722712296889241164925611)
      ·
        refine ⟨47584068445333861747388417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31722712296889241164925611 47584068445333861747388417)
        ·
          refine ⟨35688051334000396310541313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47584068445333861747388417 35688051334000396310541313)
          ·
            refine ⟨26766038500500297232905985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35688051334000396310541313 26766038500500297232905985)
            ·
              refine ⟨20074528875375222924679489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26766038500500297232905985 20074528875375222924679489)
              ·
                refine ⟨15055896656531417193509617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20074528875375222924679489 15055896656531417193509617)
                ·
                  refine ⟨11291922492398562895132213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15055896656531417193509617 11291922492398562895132213)
                  ·
                    refine ⟨1058617733662365271418645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11291922492398562895132213 1058617733662365271418645)
                    ·
                      rfl

theorem cell22_3092476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_3092476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092476 prefixEnd_3092476 := by exact prefixLift 3092476
  have htrace : WordTrace (prefixWord ++ tailWord_3092476) baseStart_3092476 baseEnd_3092476 := by
    simpa [prefixWord, tailWord_3092476, baseEnd_3092476] using wordTrace_append hprefix tailTrace_3092476
  have hstable : (prefixWord ++ tailWord_3092476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092476).length < 2 ^ (prefixWord ++ tailWord_3092476).sum := by decide
  have hdescent : baseEnd_3092476 < baseStart_3092476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092491 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 5, 4]
def baseStart_3092491 : Nat := 118140960795 + 3092491 * 2 ^ 59
def prefixEnd_3092491 : Nat := 4983230072969 + 3 ^ 40 * 3092491 * 2
def baseEnd_3092491 : Nat := 1058622868468910232293599

theorem tailTrace_3092491 : CollatzResearch.WordTrace tailWord_3092491 prefixEnd_3092491 1058622868468910232293599 := by
  unfold tailWord_3092491
  simp only [CollatzResearch.WordTrace]
  refine ⟨112792413039440737259309327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75194942026293824839539551 112792413039440737259309327)
  ·
    refine ⟨169188619559161105888963991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112792413039440737259309327 169188619559161105888963991)
    ·
      refine ⟨253782929338741658833445987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169188619559161105888963991 253782929338741658833445987)
      ·
        refine ⟨380674394008112488250168981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253782929338741658833445987 380674394008112488250168981)
        ·
          refine ⟨17844112219130272886726671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 380674394008112488250168981 17844112219130272886726671)
          ·
            refine ⟨26766168328695409330090007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17844112219130272886726671 26766168328695409330090007)
            ·
              refine ⟨40149252493043113995135011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26766168328695409330090007 40149252493043113995135011)
              ·
                refine ⟨60223878739564670992702517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40149252493043113995135011 60223878739564670992702517)
                ·
                  refine ⟨5645988631834187905565861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60223878739564670992702517 5645988631834187905565861)
                  ·
                    refine ⟨1058622868468910232293599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5645988631834187905565861 1058622868468910232293599)
                    ·
                      rfl

theorem cell22_3092491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 5, 4].length) (baseStart_3092491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092491 prefixEnd_3092491 := by exact prefixLift 3092491
  have htrace : WordTrace (prefixWord ++ tailWord_3092491) baseStart_3092491 baseEnd_3092491 := by
    simpa [prefixWord, tailWord_3092491, baseEnd_3092491] using wordTrace_append hprefix tailTrace_3092491
  have hstable : (prefixWord ++ tailWord_3092491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092491).length < 2 ^ (prefixWord ++ tailWord_3092491).sum := by decide
  have hdescent : baseEnd_3092491 < baseStart_3092491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092506 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 8]
def baseStart_3092506 : Nat := 118140960795 + 3092506 * 2 ^ 59
def prefixEnd_3092506 : Nat := 4983230072969 + 3 ^ 40 * 3092506 * 2
def baseEnd_3092506 : Nat := 352876001091818397722851

theorem tailTrace_3092506 : CollatzResearch.WordTrace tailWord_3092506 prefixEnd_3092506 352876001091818397722851 := by
  unfold tailWord_3092506
  simp only [CollatzResearch.WordTrace]
  refine ⟨28198240033596598705276343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75195306756257596547403581 28198240033596598705276343)
  ·
    refine ⟨42297360050394898057914515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28198240033596598705276343 42297360050394898057914515)
    ·
      refine ⟨63446040075592347086871773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42297360050394898057914515 63446040075592347086871773)
      ·
        refine ⟨23792265028347130157576915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63446040075592347086871773 23792265028347130157576915)
        ·
          refine ⟨35688397542520695236365373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23792265028347130157576915 35688397542520695236365373)
          ·
            refine ⟨13383149078445260713637015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35688397542520695236365373 13383149078445260713637015)
            ·
              refine ⟨20074723617667891070455523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13383149078445260713637015 20074723617667891070455523)
              ·
                refine ⟨30112085426501836605683285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20074723617667891070455523 30112085426501836605683285)
                ·
                  refine ⟨352876001091818397722851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30112085426501836605683285 352876001091818397722851)
                  ·
                    rfl

theorem cell22_3092506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_3092506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092506 prefixEnd_3092506 := by exact prefixLift 3092506
  have htrace : WordTrace (prefixWord ++ tailWord_3092506) baseStart_3092506 baseEnd_3092506 := by
    simpa [prefixWord, tailWord_3092506, baseEnd_3092506] using wordTrace_append hprefix tailTrace_3092506
  have hstable : (prefixWord ++ tailWord_3092506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092506).length < 2 ^ (prefixWord ++ tailWord_3092506).sum := by decide
  have hdescent : baseEnd_3092506 < baseStart_3092506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092508 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_3092508 : Nat := 118140960795 + 3092508 * 2 ^ 59
def prefixEnd_3092508 : Nat := 4983230072969 + 3 ^ 40 * 3092508 * 2
def baseEnd_3092508 : Nat := 1058628687916327854618547

theorem tailTrace_3092508 : CollatzResearch.WordTrace tailWord_3092508 prefixEnd_3092508 1058628687916327854618547 := by
  unfold tailWord_3092508
  simp only [CollatzResearch.WordTrace]
  refine ⟨56396516540189574581339089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75195355386919432775118785 56396516540189574581339089)
  ·
    refine ⟨42297387405142180936004317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56396516540189574581339089 42297387405142180936004317)
    ·
      refine ⟨15861520276928317851001619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42297387405142180936004317 15861520276928317851001619)
      ·
        refine ⟨23792280415392476776502429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15861520276928317851001619 23792280415392476776502429)
        ·
          refine ⟨8922105155772178791188411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23792280415392476776502429 8922105155772178791188411)
          ·
            refine ⟨13383157733658268186782617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8922105155772178791188411 13383157733658268186782617)
            ·
              refine ⟨10037368300243701140086963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13383157733658268186782617 10037368300243701140086963)
              ·
                refine ⟨15056052450365551710130445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10037368300243701140086963 15056052450365551710130445)
                ·
                  refine ⟨5646019668887081891298917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15056052450365551710130445 5646019668887081891298917)
                  ·
                    refine ⟨1058628687916327854618547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646019668887081891298917 1058628687916327854618547)
                    ·
                      rfl

theorem cell22_3092508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_3092508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092508 prefixEnd_3092508 := by exact prefixLift 3092508
  have htrace : WordTrace (prefixWord ++ tailWord_3092508) baseStart_3092508 baseEnd_3092508 := by
    simpa [prefixWord, tailWord_3092508, baseEnd_3092508] using wordTrace_append hprefix tailTrace_3092508
  have hstable : (prefixWord ++ tailWord_3092508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092508).length < 2 ^ (prefixWord ++ tailWord_3092508).sum := by decide
  have hdescent : baseEnd_3092508 < baseStart_3092508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092551 : List Nat := [1, 1, 4, 1, 3, 1, 2, 9]
def baseStart_3092551 : Nat := 118140960795 + 3092551 * 2 ^ 59
def prefixEnd_3092551 : Nat := 4983230072969 + 3 ^ 40 * 3092551 * 2
def baseEnd_3092551 : Nat := 117627045299454452865935

theorem tailTrace_3092551 : CollatzResearch.WordTrace tailWord_3092551 prefixEnd_3092551 117627045299454452865935 := by
  unfold tailWord_3092551
  simp only [CollatzResearch.WordTrace]
  refine ⟨112794601419223367506493507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75196400946148911670995671 112794601419223367506493507)
  ·
    refine ⟨169191902128835051259740261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112794601419223367506493507 169191902128835051259740261)
    ·
      refine ⟨31723481649156572111201299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169191902128835051259740261 31723481649156572111201299)
      ·
        refine ⟨47585222473734858166801949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31723481649156572111201299 47585222473734858166801949)
        ·
          refine ⟨17844458427650571812550731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47585222473734858166801949 17844458427650571812550731)
          ·
            refine ⟨26766687641475857718826097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17844458427650571812550731 26766687641475857718826097)
            ·
              refine ⟨20075015731106893289119573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26766687641475857718826097 20075015731106893289119573)
              ·
                refine ⟨117627045299454452865935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20075015731106893289119573 117627045299454452865935)
                ·
                  rfl

theorem cell22_3092551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 9].length) (baseStart_3092551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092551 prefixEnd_3092551 := by exact prefixLift 3092551
  have htrace : WordTrace (prefixWord ++ tailWord_3092551) baseStart_3092551 baseEnd_3092551 := by
    simpa [prefixWord, tailWord_3092551, baseEnd_3092551] using wordTrace_append hprefix tailTrace_3092551
  have hstable : (prefixWord ++ tailWord_3092551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092551).length < 2 ^ (prefixWord ++ tailWord_3092551).sum := by decide
  have hdescent : baseEnd_3092551 < baseStart_3092551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092568 : List Nat := [2, 1, 2, 2, 1, 4, 4, 6]
def baseStart_3092568 : Nat := 118140960795 + 3092568 * 2 ^ 59
def prefixEnd_3092568 : Nat := 4983230072969 + 3 ^ 40 * 3092568 * 2
def baseEnd_3092568 : Nat := 117627691904723077568707

theorem tailTrace_3092568 : CollatzResearch.WordTrace tailWord_3092568 prefixEnd_3092568 117627691904723077568707 := by
  unfold tailWord_3092568
  simp only [CollatzResearch.WordTrace]
  refine ⟨56397610730080889704931179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75196814306774519606574905 56397610730080889704931179)
  ·
    refine ⟨84596416095121334557396769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56397610730080889704931179 84596416095121334557396769)
    ·
      refine ⟨63447312071341000918047577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84596416095121334557396769 63447312071341000918047577)
      ·
        refine ⟨47585484053505750688535683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63447312071341000918047577 47585484053505750688535683)
        ·
          refine ⟨71378226080258626032803525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47585484053505750688535683 71378226080258626032803525)
          ·
            refine ⟨13383417390048492381150661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71378226080258626032803525 13383417390048492381150661)
            ·
              refine ⟨2509390760634092321465749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13383417390048492381150661 2509390760634092321465749)
              ·
                refine ⟨117627691904723077568707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2509390760634092321465749 117627691904723077568707)
                ·
                  rfl

theorem cell22_3092568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 6].length) (baseStart_3092568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092568 prefixEnd_3092568 := by exact prefixLift 3092568
  have htrace : WordTrace (prefixWord ++ tailWord_3092568) baseStart_3092568 baseEnd_3092568 := by
    simpa [prefixWord, tailWord_3092568, baseEnd_3092568] using wordTrace_append hprefix tailTrace_3092568
  have hstable : (prefixWord ++ tailWord_3092568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092568).length < 2 ^ (prefixWord ++ tailWord_3092568).sum := by decide
  have hdescent : baseEnd_3092568 < baseStart_3092568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092647 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 5]
def baseStart_3092647 : Nat := 118140960795 + 3092647 * 2 ^ 59
def prefixEnd_3092647 : Nat := 4983230072969 + 3 ^ 40 * 3092647 * 2
def baseEnd_3092647 : Nat := 352892090152325941797707

theorem tailTrace_3092647 : CollatzResearch.WordTrace tailWord_3092647 prefixEnd_3092647 352892090152325941797707 := by
  unfold tailWord_3092647
  simp only [CollatzResearch.WordTrace]
  refine ⟨112798102826875575901988195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75198735217917050601325463 112798102826875575901988195)
  ·
    refine ⟨169197154240313363852982293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112798102826875575901988195 169197154240313363852982293)
    ·
      refine ⟨7931116605014688930608545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169197154240313363852982293 7931116605014688930608545)
      ·
        refine ⟨5948337453761016697956409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7931116605014688930608545 5948337453761016697956409)
        ·
          refine ⟨4461253090320762523467307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5948337453761016697956409 4461253090320762523467307)
          ·
            refine ⟨6691879635481143785200961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461253090320762523467307 6691879635481143785200961)
            ·
              refine ⟨5018909726610857838900721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6691879635481143785200961 5018909726610857838900721)
              ·
                refine ⟨3764182294958143379175541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5018909726610857838900721 3764182294958143379175541)
                ·
                  refine ⟨352892090152325941797707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3764182294958143379175541 352892090152325941797707)
                  ·
                    rfl

theorem cell22_3092647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 5].length) (baseStart_3092647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092647 prefixEnd_3092647 := by exact prefixLift 3092647
  have htrace : WordTrace (prefixWord ++ tailWord_3092647) baseStart_3092647 baseEnd_3092647 := by
    simpa [prefixWord, tailWord_3092647, baseEnd_3092647] using wordTrace_append hprefix tailTrace_3092647
  have hstable : (prefixWord ++ tailWord_3092647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092647).length < 2 ^ (prefixWord ++ tailWord_3092647).sum := by decide
  have hdescent : baseEnd_3092647 < baseStart_3092647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092658 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 6]
def baseStart_3092658 : Nat := 118140960795 + 3092658 * 2 ^ 59
def prefixEnd_3092658 : Nat := 4983230072969 + 3 ^ 40 * 3092658 * 2
def baseEnd_3092658 : Nat := 352893345327259154456029

theorem tailTrace_3092658 : CollatzResearch.WordTrace tailWord_3092658 prefixEnd_3092658 352893345327259154456029 := by
  unfold tailWord_3092658
  simp only [CollatzResearch.WordTrace]
  refine ⟨28199626007458931195159657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75199002686557149853759085 28199626007458931195159657)
  ·
    refine ⟨21149719505594198396369743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28199626007458931195159657 21149719505594198396369743)
    ·
      refine ⟨31724579258391297594554615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21149719505594198396369743 31724579258391297594554615)
      ·
        refine ⟨47586868887586946391831923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31724579258391297594554615 47586868887586946391831923)
        ·
          refine ⟨71380303331380419587747885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47586868887586946391831923 71380303331380419587747885)
          ·
            refine ⟨26767613749267657345405457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71380303331380419587747885 26767613749267657345405457)
            ·
              refine ⟨20075710311950743009054093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26767613749267657345405457 20075710311950743009054093)
              ·
                refine ⟨7528391366981528628395285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20075710311950743009054093 7528391366981528628395285)
                ·
                  refine ⟨352893345327259154456029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7528391366981528628395285 352893345327259154456029)
                  ·
                    rfl

theorem cell22_3092658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_3092658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092658 prefixEnd_3092658 := by exact prefixLift 3092658
  have htrace : WordTrace (prefixWord ++ tailWord_3092658) baseStart_3092658 baseEnd_3092658 := by
    simpa [prefixWord, tailWord_3092658, baseEnd_3092658] using wordTrace_append hprefix tailTrace_3092658
  have hstable : (prefixWord ++ tailWord_3092658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092658).length < 2 ^ (prefixWord ++ tailWord_3092658).sum := by decide
  have hdescent : baseEnd_3092658 < baseStart_3092658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092690 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3092690 : Nat := 118140960795 + 3092690 * 2 ^ 59
def prefixEnd_3092690 : Nat := 4983230072969 + 3 ^ 40 * 3092690 * 2
def baseEnd_3092690 : Nat := 1058690990235740046567989

theorem tailTrace_3092690 : CollatzResearch.WordTrace tailWord_3092690 prefixEnd_3092690 1058690990235740046567989 := by
  unfold tailWord_3092690
  simp only [CollatzResearch.WordTrace]
  refine ⟨28199917791429948561450881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75199780777146529497202349 28199917791429948561450881)
  ·
    refine ⟨21149938343572461421088161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28199917791429948561450881 21149938343572461421088161)
    ·
      refine ⟨15862453757679346065816121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21149938343572461421088161 15862453757679346065816121)
      ·
        refine ⟨11896840318259509549362091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15862453757679346065816121 11896840318259509549362091)
        ·
          refine ⟨17845260477389264324043137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11896840318259509549362091 17845260477389264324043137)
          ·
            refine ⟨13383945358041948243032353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17845260477389264324043137 13383945358041948243032353)
            ·
              refine ⟨10037959018531461182274265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13383945358041948243032353 10037959018531461182274265)
              ·
                refine ⟨7528469263898595886705699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10037959018531461182274265 7528469263898595886705699)
                ·
                  refine ⟨11292703895847893830058549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528469263898595886705699 11292703895847893830058549)
                  ·
                    refine ⟨1058690990235740046567989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11292703895847893830058549 1058690990235740046567989)
                    ·
                      rfl

theorem cell22_3092690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3092690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092690 prefixEnd_3092690 := by exact prefixLift 3092690
  have htrace : WordTrace (prefixWord ++ tailWord_3092690) baseStart_3092690 baseEnd_3092690 := by
    simpa [prefixWord, tailWord_3092690, baseEnd_3092690] using wordTrace_append hprefix tailTrace_3092690
  have hstable : (prefixWord ++ tailWord_3092690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092690).length < 2 ^ (prefixWord ++ tailWord_3092690).sum := by decide
  have hdescent : baseEnd_3092690 < baseStart_3092690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092694 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3092694 : Nat := 118140960795 + 3092694 * 2 ^ 59
def prefixEnd_3092694 : Nat := 4983230072969 + 3 ^ 40 * 3092694 * 2
def baseEnd_3092694 : Nat := 1058692359517485369467977

theorem tailTrace_3092694 : CollatzResearch.WordTrace tailWord_3092694 prefixEnd_3092694 1058692359517485369467977 := by
  unfold tailWord_3092694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7049988566106581433059321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75199878038470201952632757 7049988566106581433059321)
  ·
    refine ⟨5287491424579936074794491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7049988566106581433059321 5287491424579936074794491)
    ·
      refine ⟨7931237136869904112191737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5287491424579936074794491 7931237136869904112191737)
      ·
        refine ⟨5948427852652428084143803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7931237136869904112191737 5948427852652428084143803)
        ·
          refine ⟨8922641778978642126215705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5948427852652428084143803 8922641778978642126215705)
          ·
            refine ⟨6691981334233981594661779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8922641778978642126215705 6691981334233981594661779)
            ·
              refine ⟨10037972001350972391992669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6691981334233981594661779 10037972001350972391992669)
              ·
                refine ⟨3764239500506614646997251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10037972001350972391992669 3764239500506614646997251)
                ·
                  refine ⟨5646359250759921970495877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764239500506614646997251 5646359250759921970495877)
                  ·
                    refine ⟨1058692359517485369467977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646359250759921970495877 1058692359517485369467977)
                    ·
                      rfl

theorem cell22_3092694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3092694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092694 prefixEnd_3092694 := by exact prefixLift 3092694
  have htrace : WordTrace (prefixWord ++ tailWord_3092694) baseStart_3092694 baseEnd_3092694 := by
    simpa [prefixWord, tailWord_3092694, baseEnd_3092694] using wordTrace_append hprefix tailTrace_3092694
  have hstable : (prefixWord ++ tailWord_3092694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092694).length < 2 ^ (prefixWord ++ tailWord_3092694).sum := by decide
  have hdescent : baseEnd_3092694 < baseStart_3092694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092733 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3092733 : Nat := 118140960795 + 3092733 * 2 ^ 59
def prefixEnd_3092733 : Nat := 4983230072969 + 3 ^ 40 * 3092733 * 2
def baseEnd_3092733 : Nat := 1058705710014502267742857

theorem tailTrace_3092733 : CollatzResearch.WordTrace tailWord_3092733 prefixEnd_3092733 1058705710014502267742857 := by
  unfold tailWord_3092733
  simp only [CollatzResearch.WordTrace]
  refine ⟨112801239504564012589618853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75200826336376008393079235 112801239504564012589618853)
  ·
    refine ⟨21150232407105752360553535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112801239504564012589618853 21150232407105752360553535)
    ·
      refine ⟨31725348610658628540830303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21150232407105752360553535 31725348610658628540830303)
      ·
        refine ⟨47588022915987942811245455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31725348610658628540830303 47588022915987942811245455)
        ·
          refine ⟨71382034373981914216868183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47588022915987942811245455 71382034373981914216868183)
          ·
            refine ⟨107073051560972871325302275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71382034373981914216868183 107073051560972871325302275)
            ·
              refine ⟨160609577341459306987953413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107073051560972871325302275 160609577341459306987953413)
              ·
                refine ⟨30114295751523620060241265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160609577341459306987953413 30114295751523620060241265)
                ·
                  refine ⟨22585721813642715045180949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30114295751523620060241265 22585721813642715045180949)
                  ·
                    refine ⟨1058705710014502267742857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22585721813642715045180949 1058705710014502267742857)
                    ·
                      rfl

theorem cell22_3092733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3092733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092733 prefixEnd_3092733 := by exact prefixLift 3092733
  have htrace : WordTrace (prefixWord ++ tailWord_3092733) baseStart_3092733 baseEnd_3092733 := by
    simpa [prefixWord, tailWord_3092733, baseEnd_3092733] using wordTrace_append hprefix tailTrace_3092733
  have hstable : (prefixWord ++ tailWord_3092733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092733).length < 2 ^ (prefixWord ++ tailWord_3092733).sum := by decide
  have hdescent : baseEnd_3092733 < baseStart_3092733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092735 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 3, 3]
def baseStart_3092735 : Nat := 118140960795 + 3092735 * 2 ^ 59
def prefixEnd_3092735 : Nat := 4983230072969 + 3 ^ 40 * 3092735 * 2
def baseEnd_3092735 : Nat := 1058706394655374929192851

theorem tailTrace_3092735 : CollatzResearch.WordTrace tailWord_3092735 prefixEnd_3092735 1058706394655374929192851 := by
  unfold tailWord_3092735
  simp only [CollatzResearch.WordTrace]
  refine ⟨112801312450556766931191659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75200874967037844620794439 112801312450556766931191659)
  ·
    refine ⟨169201968675835150396787489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112801312450556766931191659 169201968675835150396787489)
    ·
      refine ⟨126901476506876362797590617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169201968675835150396787489 126901476506876362797590617)
      ·
        refine ⟨95176107380157272098192963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126901476506876362797590617 95176107380157272098192963)
        ·
          refine ⟨142764161070235908147289445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95176107380157272098192963 142764161070235908147289445)
          ·
            refine ⟨26768280200669232777616771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142764161070235908147289445 26768280200669232777616771)
            ·
              refine ⟨40152420301003849166425157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26768280200669232777616771 40152420301003849166425157)
              ·
                refine ⟨7528578806438221718704717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40152420301003849166425157 7528578806438221718704717)
                ·
                  refine ⟨2823217052414333144514269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7528578806438221718704717 2823217052414333144514269)
                  ·
                    refine ⟨1058706394655374929192851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823217052414333144514269 1058706394655374929192851)
                    ·
                      rfl

theorem cell22_3092735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_3092735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092735 prefixEnd_3092735 := by exact prefixLift 3092735
  have htrace : WordTrace (prefixWord ++ tailWord_3092735) baseStart_3092735 baseEnd_3092735 := by
    simpa [prefixWord, tailWord_3092735, baseEnd_3092735] using wordTrace_append hprefix tailTrace_3092735
  have hstable : (prefixWord ++ tailWord_3092735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092735).length < 2 ^ (prefixWord ++ tailWord_3092735).sum := by decide
  have hdescent : baseEnd_3092735 < baseStart_3092735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092748 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 9]
def baseStart_3092748 : Nat := 118140960795 + 3092748 * 2 ^ 59
def prefixEnd_3092748 : Nat := 4983230072969 + 3 ^ 40 * 3092748 * 2
def baseEnd_3092748 : Nat := 352903614940349076205937

theorem tailTrace_3092748 : CollatzResearch.WordTrace tailWord_3092748 prefixEnd_3092748 352903614940349076205937 := by
  unfold tailWord_3092748
  simp only [CollatzResearch.WordTrace]
  refine ⟨56400893299754835075707449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75201191066339780100943265 56400893299754835075707449)
  ·
    refine ⟨42300669974816126306780587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56400893299754835075707449 42300669974816126306780587)
    ·
      refine ⟨63451004962224189460170881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42300669974816126306780587 63451004962224189460170881)
      ·
        refine ⟨47588253721668142095128161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63451004962224189460170881 47588253721668142095128161)
        ·
          refine ⟨35691190291251106571346121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47588253721668142095128161 35691190291251106571346121)
          ·
            refine ⟨26768392718438329928509591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35691190291251106571346121 26768392718438329928509591)
            ·
              refine ⟨40152589077657494892764387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26768392718438329928509591 40152589077657494892764387)
              ·
                refine ⟨60228883616486242339146581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40152589077657494892764387 60228883616486242339146581)
                ·
                  refine ⟨352903614940349076205937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60228883616486242339146581 352903614940349076205937)
                  ·
                    rfl

theorem cell22_3092748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_3092748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092748 prefixEnd_3092748 := by exact prefixLift 3092748
  have htrace : WordTrace (prefixWord ++ tailWord_3092748) baseStart_3092748 baseEnd_3092748 := by
    simpa [prefixWord, tailWord_3092748, baseEnd_3092748] using wordTrace_append hprefix tailTrace_3092748
  have hstable : (prefixWord ++ tailWord_3092748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092748).length < 2 ^ (prefixWord ++ tailWord_3092748).sum := by decide
  have hdescent : baseEnd_3092748 < baseStart_3092748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092763 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 4, 5]
def baseStart_3092763 : Nat := 118140960795 + 3092763 * 2 ^ 59
def prefixEnd_3092763 : Nat := 4983230072969 + 3 ^ 40 * 3092763 * 2
def baseEnd_3092763 : Nat := 1058715979627592189492765

theorem tailTrace_3092763 : CollatzResearch.WordTrace tailWord_3092763 prefixEnd_3092763 1058715979627592189492765 := by
  unfold tailWord_3092763
  simp only [CollatzResearch.WordTrace]
  refine ⟨112802333694455327713210943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75201555796303551808807295 112802333694455327713210943)
  ·
    refine ⟨169203500541682991569816415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112802333694455327713210943 169203500541682991569816415)
    ·
      refine ⟨253805250812524487354724623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169203500541682991569816415 253805250812524487354724623)
      ·
        refine ⟨380707876218786731032086935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253805250812524487354724623 380707876218786731032086935)
        ·
          refine ⟨571061814328180096548130403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380707876218786731032086935 571061814328180096548130403)
          ·
            refine ⟨856592721492270144822195605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571061814328180096548130403 856592721492270144822195605)
            ·
              refine ⟨40152783819950163038540419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 856592721492270144822195605 40152783819950163038540419)
              ·
                refine ⟨60229175729925244557810629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40152783819950163038540419 60229175729925244557810629)
                ·
                  refine ⟨11292970449360983354589493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60229175729925244557810629 11292970449360983354589493)
                  ·
                    refine ⟨1058715979627592189492765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11292970449360983354589493 1058715979627592189492765)
                    ·
                      rfl

theorem cell22_3092763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 5].length) (baseStart_3092763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092763 prefixEnd_3092763 := by exact prefixLift 3092763
  have htrace : WordTrace (prefixWord ++ tailWord_3092763) baseStart_3092763 baseEnd_3092763 := by
    simpa [prefixWord, tailWord_3092763, baseEnd_3092763] using wordTrace_append hprefix tailTrace_3092763
  have hstable : (prefixWord ++ tailWord_3092763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092763).length < 2 ^ (prefixWord ++ tailWord_3092763).sum := by decide
  have hdescent : baseEnd_3092763 < baseStart_3092763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092775 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3092775 : Nat := 118140960795 + 3092775 * 2 ^ 59
def prefixEnd_3092775 : Nat := 4983230072969 + 3 ^ 40 * 3092775 * 2
def baseEnd_3092775 : Nat := 1058720087472828158192729

theorem tailTrace_3092775 : CollatzResearch.WordTrace tailWord_3092775 prefixEnd_3092775 1058720087472828158192729 := by
  unfold tailWord_3092775
  simp only [CollatzResearch.WordTrace]
  refine ⟨112802771370411853762647779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75201847580274569175098519 112802771370411853762647779)
  ·
    refine ⟨169204157055617780643971669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112802771370411853762647779 169204157055617780643971669)
    ·
      refine ⟨1982861215495520866921543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 169204157055617780643971669 1982861215495520866921543)
      ·
        refine ⟨2974291823243281300382315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982861215495520866921543 2974291823243281300382315)
        ·
          refine ⟨4461437734864921950573473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974291823243281300382315 4461437734864921950573473)
          ·
            refine ⟨3346078301148691462930105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4461437734864921950573473 3346078301148691462930105)
            ·
              refine ⟨2509558725861518597197579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346078301148691462930105 2509558725861518597197579)
              ·
                refine ⟨3764338088792277895796369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509558725861518597197579 3764338088792277895796369)
                ·
                  refine ⟨2823253566594208421847277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3764338088792277895796369 2823253566594208421847277)
                  ·
                    refine ⟨1058720087472828158192729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823253566594208421847277 1058720087472828158192729)
                    ·
                      rfl

theorem cell22_3092775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3092775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092775 prefixEnd_3092775 := by exact prefixLift 3092775
  have htrace : WordTrace (prefixWord ++ tailWord_3092775) baseStart_3092775 baseEnd_3092775 := by
    simpa [prefixWord, tailWord_3092775, baseEnd_3092775] using wordTrace_append hprefix tailTrace_3092775
  have hstable : (prefixWord ++ tailWord_3092775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092775).length < 2 ^ (prefixWord ++ tailWord_3092775).sum := by decide
  have hdescent : baseEnd_3092775 < baseStart_3092775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092842 : List Nat := [3, 1, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_3092842 : Nat := 118140960795 + 3092842 * 2 ^ 59
def prefixEnd_3092842 : Nat := 4983230072969 + 3 ^ 40 * 3092842 * 2
def baseEnd_3092842 : Nat := 1058743022942062316767523

theorem tailTrace_3092842 : CollatzResearch.WordTrace tailWord_3092842 prefixEnd_3092842 1058743022942062316767523 := by
  unfold tailWord_3092842
  simp only [CollatzResearch.WordTrace]
  refine ⟨28201303765292281051334195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75203476707446082803557853 28201303765292281051334195)
  ·
    refine ⟨42301955647938421577001293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28201303765292281051334195 42301955647938421577001293)
    ·
      refine ⟨15863233367976908091375485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42301955647938421577001293 15863233367976908091375485)
      ·
        refine ⟨5948712512991340534265807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15863233367976908091375485 5948712512991340534265807)
        ·
          refine ⟨8923068769487010801398711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5948712512991340534265807 8923068769487010801398711)
          ·
            refine ⟨13384603154230516202098067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923068769487010801398711 13384603154230516202098067)
            ·
              refine ⟨20076904731345774303147101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13384603154230516202098067 20076904731345774303147101)
              ·
                refine ⟨7528839274254665363680163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20076904731345774303147101 7528839274254665363680163)
                ·
                  refine ⟨11293258911381998045520245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7528839274254665363680163 11293258911381998045520245)
                  ·
                    refine ⟨1058743022942062316767523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11293258911381998045520245 1058743022942062316767523)
                    ·
                      rfl

theorem cell22_3092842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_3092842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092842 prefixEnd_3092842 := by exact prefixLift 3092842
  have htrace : WordTrace (prefixWord ++ tailWord_3092842) baseStart_3092842 baseEnd_3092842 := by
    simpa [prefixWord, tailWord_3092842, baseEnd_3092842] using wordTrace_append hprefix tailTrace_3092842
  have hstable : (prefixWord ++ tailWord_3092842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092842).length < 2 ^ (prefixWord ++ tailWord_3092842).sum := by decide
  have hdescent : baseEnd_3092842 < baseStart_3092842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092887 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 3, 3]
def baseStart_3092887 : Nat := 118140960795 + 3092887 * 2 ^ 59
def prefixEnd_3092887 : Nat := 4983230072969 + 3 ^ 40 * 3092887 * 2
def baseEnd_3092887 : Nat := 1058758427361697199392385

theorem tailTrace_3092887 : CollatzResearch.WordTrace tailWord_3092887 prefixEnd_3092887 1058758427361697199392385 := by
  unfold tailWord_3092887
  simp only [CollatzResearch.WordTrace]
  refine ⟨112806856346006096890724915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75204570897337397927149943 112806856346006096890724915)
  ·
    refine ⟨169210284519009145336087373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112806856346006096890724915 169210284519009145336087373)
    ·
      refine ⟨63453856694628429501032765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169210284519009145336087373 63453856694628429501032765)
      ·
        refine ⟨23795196260485661062887287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63453856694628429501032765 23795196260485661062887287)
        ·
          refine ⟨35692794390728491594330931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23795196260485661062887287 35692794390728491594330931)
          ·
            refine ⟨53539191586092737391496397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35692794390728491594330931 53539191586092737391496397)
            ·
              refine ⟨20077196844784776521811149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53539191586092737391496397 20077196844784776521811149)
              ·
                refine ⟨7528948816794291195679181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20077196844784776521811149 7528948816794291195679181)
                ·
                  refine ⟨2823355806297859198379693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7528948816794291195679181 2823355806297859198379693)
                  ·
                    refine ⟨1058758427361697199392385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823355806297859198379693 1058758427361697199392385)
                    ·
                      rfl

theorem cell22_3092887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_3092887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092887 prefixEnd_3092887 := by exact prefixLift 3092887
  have htrace : WordTrace (prefixWord ++ tailWord_3092887) baseStart_3092887 baseEnd_3092887 := by
    simpa [prefixWord, tailWord_3092887, baseEnd_3092887] using wordTrace_append hprefix tailTrace_3092887
  have hstable : (prefixWord ++ tailWord_3092887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092887).length < 2 ^ (prefixWord ++ tailWord_3092887).sum := by decide
  have hdescent : baseEnd_3092887 < baseStart_3092887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092906 : List Nat := [3, 1, 6, 1, 1, 1, 1, 8]
def baseStart_3092906 : Nat := 118140960795 + 3092906 * 2 ^ 59
def prefixEnd_3092906 : Nat := 4983230072969 + 3 ^ 40 * 3092906 * 2
def baseEnd_3092906 : Nat := 117640547938887498129703

theorem tailTrace_3092906 : CollatzResearch.WordTrace tailWord_3092906 prefixEnd_3092906 117640547938887498129703 := by
  unfold tailWord_3092906
  simp only [CollatzResearch.WordTrace]
  refine ⟨28201887333234315783916643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75205032888624842090444381 28201887333234315783916643)
  ·
    refine ⟨42302830999851473675874965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28201887333234315783916643 42302830999851473675874965)
    ·
      refine ⟨1982945203118037828556639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42302830999851473675874965 1982945203118037828556639)
      ·
        refine ⟨2974417804677056742834959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1982945203118037828556639 2974417804677056742834959)
        ·
          refine ⟨4461626707015585114252439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2974417804677056742834959 4461626707015585114252439)
          ·
            refine ⟨6692440060523377671378659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4461626707015585114252439 6692440060523377671378659)
            ·
              refine ⟨10038660090785066507067989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692440060523377671378659 10038660090785066507067989)
              ·
                refine ⟨117640547938887498129703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10038660090785066507067989 117640547938887498129703)
                ·
                  rfl

theorem cell22_3092906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_3092906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092906 prefixEnd_3092906 := by exact prefixLift 3092906
  have htrace : WordTrace (prefixWord ++ tailWord_3092906) baseStart_3092906 baseEnd_3092906 := by
    simpa [prefixWord, tailWord_3092906, baseEnd_3092906] using wordTrace_append hprefix tailTrace_3092906
  have hstable : (prefixWord ++ tailWord_3092906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092906).length < 2 ^ (prefixWord ++ tailWord_3092906).sum := by decide
  have hdescent : baseEnd_3092906 < baseStart_3092906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092921 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 1, 3]
def baseStart_3092921 : Nat := 118140960795 + 3092921 * 2 ^ 59
def prefixEnd_3092921 : Nat := 4983230072969 + 3 ^ 40 * 3092921 * 2
def baseEnd_3092921 : Nat := 1058770066256532444042281

theorem tailTrace_3092921 : CollatzResearch.WordTrace tailWord_3092921 prefixEnd_3092921 1058770066256532444042281 := by
  unfold tailWord_3092921
  simp only [CollatzResearch.WordTrace]
  refine ⟨112808096427882920697462617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75205397618588613798308411 112808096427882920697462617)
  ·
    refine ⟨84606072320912190523096963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112808096427882920697462617 84606072320912190523096963)
    ·
      refine ⟨126909108481368285784645445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84606072320912190523096963 126909108481368285784645445)
      ·
        refine ⟨23795457840256553584621021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126909108481368285784645445 23795457840256553584621021)
        ·
          refine ⟨8923296690096207594232883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23795457840256553584621021 8923296690096207594232883)
          ·
            refine ⟨13384945035144311391349325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923296690096207594232883 13384945035144311391349325)
            ·
              refine ⟨5019354388179116771755997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13384945035144311391349325 5019354388179116771755997)
              ·
                refine ⟨1882257895567168789408499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5019354388179116771755997 1882257895567168789408499)
                ·
                  refine ⟨2823386843350753184112749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882257895567168789408499 2823386843350753184112749)
                  ·
                    refine ⟨1058770066256532444042281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823386843350753184112749 1058770066256532444042281)
                    ·
                      rfl

theorem cell22_3092921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_3092921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092921 prefixEnd_3092921 := by exact prefixLift 3092921
  have htrace : WordTrace (prefixWord ++ tailWord_3092921) baseStart_3092921 baseEnd_3092921 := by
    simpa [prefixWord, tailWord_3092921, baseEnd_3092921] using wordTrace_append hprefix tailTrace_3092921
  have hstable : (prefixWord ++ tailWord_3092921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092921).length < 2 ^ (prefixWord ++ tailWord_3092921).sum := by decide
  have hdescent : baseEnd_3092921 < baseStart_3092921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092977 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_3092977 : Nat := 118140960795 + 3092977 * 2 ^ 59
def prefixEnd_3092977 : Nat := 4983230072969 + 3 ^ 40 * 3092977 * 2
def baseEnd_3092977 : Nat := 1058789236200966964642109

theorem tailTrace_3092977 : CollatzResearch.WordTrace tailWord_3092977 prefixEnd_3092977 1058789236200966964642109 := by
  unfold tailWord_3092977
  simp only [CollatzResearch.WordTrace]
  refine ⟨112810138915680042261501185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75206759277120028174334123 112810138915680042261501185)
  ·
    refine ⟨84607604186760031696125889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112810138915680042261501185 84607604186760031696125889)
    ·
      refine ⟨63455703140070023772094417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84607604186760031696125889 63455703140070023772094417)
      ·
        refine ⟨47591777355052517829070813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63455703140070023772094417 47591777355052517829070813)
        ·
          refine ⟨17846916508144694185901555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47591777355052517829070813 17846916508144694185901555)
          ·
            refine ⟨26770374762217041278852333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17846916508144694185901555 26770374762217041278852333)
            ·
              refine ⟨10038890535831390479569625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26770374762217041278852333 10038890535831390479569625)
              ·
                refine ⟨7529167901873542859677219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10038890535831390479569625 7529167901873542859677219)
                ·
                  refine ⟨11293751852810314289515829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7529167901873542859677219 11293751852810314289515829)
                  ·
                    refine ⟨1058789236200966964642109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11293751852810314289515829 1058789236200966964642109)
                    ·
                      rfl

theorem cell22_3092977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_3092977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092977 prefixEnd_3092977 := by exact prefixLift 3092977
  have htrace : WordTrace (prefixWord ++ tailWord_3092977) baseStart_3092977 baseEnd_3092977 := by
    simpa [prefixWord, tailWord_3092977, baseEnd_3092977] using wordTrace_append hprefix tailTrace_3092977
  have hstable : (prefixWord ++ tailWord_3092977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092977).length < 2 ^ (prefixWord ++ tailWord_3092977).sum := by decide
  have hdescent : baseEnd_3092977 < baseStart_3092977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092996 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 4]
def baseStart_3092996 : Nat := 118140960795 + 3092996 * 2 ^ 59
def prefixEnd_3092996 : Nat := 4983230072969 + 3 ^ 40 * 3092996 * 2
def baseEnd_3092996 : Nat := 352931913429752416139017

theorem tailTrace_3092996 : CollatzResearch.WordTrace tailWord_3092996 prefixEnd_3092996 352931913429752416139017 := by
  unfold tailWord_3092996
  simp only [CollatzResearch.WordTrace]
  refine ⟨56405415951305604253221421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75207221268407472337628561 56405415951305604253221421)
  ·
    refine ⟨21152030981739601594958033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56405415951305604253221421 21152030981739601594958033)
    ·
      refine ⟨15864023236304701196218525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21152030981739601594958033 15864023236304701196218525)
      ·
        refine ⟨5949008713614262948581947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15864023236304701196218525 5949008713614262948581947)
        ·
          refine ⟨8923513070421394422872921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949008713614262948581947 8923513070421394422872921)
          ·
            refine ⟨6692634802816045817154691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8923513070421394422872921 6692634802816045817154691)
            ·
              refine ⟨10038952204224068725732037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6692634802816045817154691 10038952204224068725732037)
              ·
                refine ⟨1882303538292012886074757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10038952204224068725732037 1882303538292012886074757)
                ·
                  refine ⟨352931913429752416139017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882303538292012886074757 352931913429752416139017)
                  ·
                    rfl

theorem cell22_3092996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_3092996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092996 prefixEnd_3092996 := by exact prefixLift 3092996
  have htrace : WordTrace (prefixWord ++ tailWord_3092996) baseStart_3092996 baseEnd_3092996 := by
    simpa [prefixWord, tailWord_3092996, baseEnd_3092996] using wordTrace_append hprefix tailTrace_3092996
  have hstable : (prefixWord ++ tailWord_3092996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092996).length < 2 ^ (prefixWord ++ tailWord_3092996).sum := by decide
  have hdescent : baseEnd_3092996 < baseStart_3092996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3092998 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3092998 : Nat := 118140960795 + 3092998 * 2 ^ 59
def prefixEnd_3092998 : Nat := 4983230072969 + 3 ^ 40 * 3092998 * 2
def baseEnd_3092998 : Nat := 1058796424930129909867045

theorem tailTrace_3092998 : CollatzResearch.WordTrace tailWord_3092998 prefixEnd_3092998 1058796424930129909867045 := by
  unfold tailWord_3092998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525340776518873839000489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 75207269899069308565343765 3525340776518873839000489)
  ·
    refine ⟨2644005582389155379250367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3525340776518873839000489 2644005582389155379250367)
    ·
      refine ⟨3966008373583733068875551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2644005582389155379250367 3966008373583733068875551)
      ·
        refine ⟨5949012560375599603313327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966008373583733068875551 5949012560375599603313327)
        ·
          refine ⟨8923518840563399404969991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949012560375599603313327 8923518840563399404969991)
          ·
            refine ⟨13385278260845099107454987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8923518840563399404969991 13385278260845099107454987)
            ·
              refine ⟨20077917391267648661182481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13385278260845099107454987 20077917391267648661182481)
              ·
                refine ⟨15058438043450736495886861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20077917391267648661182481 15058438043450736495886861)
                ·
                  refine ⟨5646914266294026185957573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15058438043450736495886861 5646914266294026185957573)
                  ·
                    refine ⟨1058796424930129909867045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5646914266294026185957573 1058796424930129909867045)
                    ·
                      rfl

theorem cell22_3092998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3092998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3092998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3092998 prefixEnd_3092998 := by exact prefixLift 3092998
  have htrace : WordTrace (prefixWord ++ tailWord_3092998) baseStart_3092998 baseEnd_3092998 := by
    simpa [prefixWord, tailWord_3092998, baseEnd_3092998] using wordTrace_append hprefix tailTrace_3092998
  have hstable : (prefixWord ++ tailWord_3092998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3092998).length < 2 ^ (prefixWord ++ tailWord_3092998).sum := by decide
  have hdescent : baseEnd_3092998 < baseStart_3092998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3092998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093056 : List Nat := [2, 1, 1, 2, 2, 2, 4, 4, 1, 3]
def baseStart_3093056 : Nat := 118140960795 + 3093056 * 2 ^ 59
def prefixEnd_3093056 : Nat := 4983230072969 + 3 ^ 40 * 3093056 * 2
def baseEnd_3093056 : Nat := 1058816279515437091916867

theorem tailTrace_3093056 : CollatzResearch.WordTrace tailWord_3093056 prefixEnd_3093056 1058816279515437091916867 := by
  unfold tailWord_3093056
  simp only [CollatzResearch.WordTrace]
  refine ⟨56406510141196919376813511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75208680188262559169084681 56406510141196919376813511)
  ·
    refine ⟨84609765211795379065220267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56406510141196919376813511 84609765211795379065220267)
    ·
      refine ⟨126914647817693068597830401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84609765211795379065220267 126914647817693068597830401)
      ·
        refine ⟨95185985863269801448372801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126914647817693068597830401 95185985863269801448372801)
        ·
          refine ⟨71389489397452351086279601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95185985863269801448372801 71389489397452351086279601)
          ·
            refine ⟨53542117048089263314709701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71389489397452351086279601 53542117048089263314709701)
            ·
              refine ⟨10039146946516736871508069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53542117048089263314709701 10039146946516736871508069)
              ·
                refine ⟨1882340052471888163407763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10039146946516736871508069 1882340052471888163407763)
                ·
                  refine ⟨2823510078707832245111645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882340052471888163407763 2823510078707832245111645)
                  ·
                    refine ⟨1058816279515437091916867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823510078707832245111645 1058816279515437091916867)
                    ·
                      rfl

theorem cell22_3093056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_3093056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093056 prefixEnd_3093056 := by exact prefixLift 3093056
  have htrace : WordTrace (prefixWord ++ tailWord_3093056) baseStart_3093056 baseEnd_3093056 := by
    simpa [prefixWord, tailWord_3093056, baseEnd_3093056] using wordTrace_append hprefix tailTrace_3093056
  have hstable : (prefixWord ++ tailWord_3093056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093056).length < 2 ^ (prefixWord ++ tailWord_3093056).sum := by decide
  have hdescent : baseEnd_3093056 < baseStart_3093056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093067 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 2, 5]
def baseStart_3093067 : Nat := 118140960795 + 3093067 * 2 ^ 59
def prefixEnd_3093067 : Nat := 4983230072969 + 3 ^ 40 * 3093067 * 2
def baseEnd_3093067 : Nat := 1058820045040236729891833

theorem tailTrace_3093067 : CollatzResearch.WordTrace tailWord_3093067 prefixEnd_3093067 1058820045040236729891833 := by
  unfold tailWord_3093067
  simp only [CollatzResearch.WordTrace]
  refine ⟨112813421485353987632277455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75208947656902658421518303 112813421485353987632277455)
  ·
    refine ⟨169220132228030981448416183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112813421485353987632277455 169220132228030981448416183)
    ·
      refine ⟨253830198342046472172624275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169220132228030981448416183 253830198342046472172624275)
      ·
        refine ⟨380745297513069708258936413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253830198342046472172624275 380745297513069708258936413)
        ·
          refine ⟨142779486567401140597101155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 380745297513069708258936413 142779486567401140597101155)
          ·
            refine ⟨214169229851101710895651733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142779486567401140597101155 214169229851101710895651733)
            ·
              refine ⟨10039182649270392698233675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214169229851101710895651733 10039182649270392698233675)
              ·
                refine ⟨15058773973905589047350513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10039182649270392698233675 15058773973905589047350513)
                ·
                  refine ⟨11294080480429191785512885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15058773973905589047350513 11294080480429191785512885)
                  ·
                    refine ⟨1058820045040236729891833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11294080480429191785512885 1058820045040236729891833)
                    ·
                      rfl

theorem cell22_3093067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 5].length) (baseStart_3093067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093067 prefixEnd_3093067 := by exact prefixLift 3093067
  have htrace : WordTrace (prefixWord ++ tailWord_3093067) baseStart_3093067 baseEnd_3093067 := by
    simpa [prefixWord, tailWord_3093067, baseEnd_3093067] using wordTrace_append hprefix tailTrace_3093067
  have hstable : (prefixWord ++ tailWord_3093067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093067).length < 2 ^ (prefixWord ++ tailWord_3093067).sum := by decide
  have hdescent : baseEnd_3093067 < baseStart_3093067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093112 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_3093112 : Nat := 118140960795 + 3093112 * 2 ^ 59
def prefixEnd_3093112 : Nat := 4983230072969 + 3 ^ 40 * 3093112 * 2
def baseEnd_3093112 : Nat := 1058835449459871612516695

theorem tailTrace_3093112 : CollatzResearch.WordTrace tailWord_3093112 prefixEnd_3093112 1058835449459871612516695 := by
  unfold tailWord_3093112
  simp only [CollatzResearch.WordTrace]
  refine ⟨56407531385095480158832795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75210041846793973545110393 56407531385095480158832795)
  ·
    refine ⟨84611297077643220238249193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56407531385095480158832795 84611297077643220238249193)
    ·
      refine ⟨63458472808232415178686895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84611297077643220238249193 63458472808232415178686895)
      ·
        refine ⟨95187709212348622768030343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63458472808232415178686895 95187709212348622768030343)
        ·
          refine ⟨142781563818522934152045515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95187709212348622768030343 142781563818522934152045515)
          ·
            refine ⟨214172345727784401228068273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142781563818522934152045515 214172345727784401228068273)
            ·
              refine ⟨160629259295838300921051205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214172345727784401228068273 160629259295838300921051205)
              ·
                refine ⟨30117986117969681422697101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 160629259295838300921051205 30117986117969681422697101)
                ·
                  refine ⟨11294244794238630533511413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30117986117969681422697101 11294244794238630533511413)
                  ·
                    refine ⟨1058835449459871612516695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11294244794238630533511413 1058835449459871612516695)
                    ·
                      rfl

theorem cell22_3093112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_3093112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093112 prefixEnd_3093112 := by exact prefixLift 3093112
  have htrace : WordTrace (prefixWord ++ tailWord_3093112) baseStart_3093112 baseEnd_3093112 := by
    simpa [prefixWord, tailWord_3093112, baseEnd_3093112] using wordTrace_append hprefix tailTrace_3093112
  have hstable : (prefixWord ++ tailWord_3093112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093112).length < 2 ^ (prefixWord ++ tailWord_3093112).sum := by decide
  have hdescent : baseEnd_3093112 < baseStart_3093112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093159 : List Nat := [1, 1, 6, 3, 11]
def baseStart_3093159 : Nat := 118140960795 + 3093159 * 2 ^ 59
def prefixEnd_3093159 : Nat := 4983230072969 + 3 ^ 40 * 3093159 * 2
def baseEnd_3093159 : Nat := 4357413738766992413957

theorem tailTrace_3093159 : CollatzResearch.WordTrace tailWord_3093159 prefixEnd_3093159 4357413738766992413957 := by
  unfold tailWord_3093159
  simp only [CollatzResearch.WordTrace]
  refine ⟨112816777001020687344626531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75211184667347124896417687 112816777001020687344626531)
  ·
    refine ⟨169225165501531031016939797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112816777001020687344626531 169225165501531031016939797)
    ·
      refine ⟨7932429632884267078919053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 169225165501531031016939797 7932429632884267078919053)
      ·
        refine ⟨2974661112331600154594645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7932429632884267078919053 2974661112331600154594645)
        ·
          refine ⟨4357413738766992413957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2974661112331600154594645 4357413738766992413957)
          ·
            rfl

theorem cell22_3093159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 11].length) (baseStart_3093159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093159 prefixEnd_3093159 := by exact prefixLift 3093159
  have htrace : WordTrace (prefixWord ++ tailWord_3093159) baseStart_3093159 baseEnd_3093159 := by
    simpa [prefixWord, tailWord_3093159, baseEnd_3093159] using wordTrace_append hprefix tailTrace_3093159
  have hstable : (prefixWord ++ tailWord_3093159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093159).length < 2 ^ (prefixWord ++ tailWord_3093159).sum := by decide
  have hdescent : baseEnd_3093159 < baseStart_3093159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093165 : List Nat := [1, 5, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3093165 : Nat := 118140960795 + 3093165 * 2 ^ 59
def prefixEnd_3093165 : Nat := 4983230072969 + 3 ^ 40 * 3093165 * 2
def baseEnd_3093165 : Nat := 352951197480999046980511

theorem tailTrace_3093165 : CollatzResearch.WordTrace tailWord_3093165 prefixEnd_3093165 352951197480999046980511 := by
  unfold tailWord_3093165
  simp only [CollatzResearch.WordTrace]
  refine ⟨112816995838998950369344949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75211330559332633579563299 112816995838998950369344949)
  ·
    refine ⟨10576593359906151597126089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 112816995838998950369344949 10576593359906151597126089)
    ·
      refine ⟨7932445019929613697844567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10576593359906151597126089 7932445019929613697844567)
      ·
        refine ⟨11898667529894420546766851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932445019929613697844567 11898667529894420546766851)
        ·
          refine ⟨17848001294841630820150277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898667529894420546766851 17848001294841630820150277)
          ·
            refine ⟨3346500242782805778778177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17848001294841630820150277 3346500242782805778778177)
            ·
              refine ⟨2509875182087104334083633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3346500242782805778778177 2509875182087104334083633)
              ·
                refine ⟨1882406386565328250562725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2509875182087104334083633 1882406386565328250562725)
                ·
                  refine ⟨352951197480999046980511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882406386565328250562725 352951197480999046980511)
                  ·
                    rfl

theorem cell22_3093165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3093165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093165 prefixEnd_3093165 := by exact prefixLift 3093165
  have htrace : WordTrace (prefixWord ++ tailWord_3093165) baseStart_3093165 baseEnd_3093165 := by
    simpa [prefixWord, tailWord_3093165, baseEnd_3093165] using wordTrace_append hprefix tailTrace_3093165
  have hstable : (prefixWord ++ tailWord_3093165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093165).length < 2 ^ (prefixWord ++ tailWord_3093165).sum := by decide
  have hdescent : baseEnd_3093165 < baseStart_3093165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093208 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 1, 3]
def baseStart_3093208 : Nat := 118140960795 + 3093208 * 2 ^ 59
def prefixEnd_3093208 : Nat := 4983230072969 + 3 ^ 40 * 3093208 * 2
def baseEnd_3093208 : Nat := 1058868312221759362116401

theorem tailTrace_3093208 : CollatzResearch.WordTrace tailWord_3093208 prefixEnd_3093208 1058868312221759362116401 := by
  unfold tailWord_3093208
  simp only [CollatzResearch.WordTrace]
  refine ⟨56409282088921584356580139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75212376118562112475440185 56409282088921584356580139)
  ·
    refine ⟨84613923133382376534870209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56409282088921584356580139 84613923133382376534870209)
    ·
      refine ⟨63460442350036782401152657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84613923133382376534870209 63460442350036782401152657)
      ·
        refine ⟨47595331762527586800864493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63460442350036782401152657 47595331762527586800864493)
        ·
          refine ⟨17848249410947845050324185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47595331762527586800864493 17848249410947845050324185)
          ·
            refine ⟨13386187058210883787743139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17848249410947845050324185 13386187058210883787743139)
            ·
              refine ⟨20079280587316325681614709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13386187058210883787743139 20079280587316325681614709)
              ·
                refine ⟨1882432555060905532651379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20079280587316325681614709 1882432555060905532651379)
                ·
                  refine ⟨2823648832591358298977069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882432555060905532651379 2823648832591358298977069)
                  ·
                    refine ⟨1058868312221759362116401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823648832591358298977069 1058868312221759362116401)
                    ·
                      rfl

theorem cell22_3093208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_3093208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093208 prefixEnd_3093208 := by exact prefixLift 3093208
  have htrace : WordTrace (prefixWord ++ tailWord_3093208) baseStart_3093208 baseEnd_3093208 := by
    simpa [prefixWord, tailWord_3093208, baseEnd_3093208] using wordTrace_append hprefix tailTrace_3093208
  have hstable : (prefixWord ++ tailWord_3093208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093208).length < 2 ^ (prefixWord ++ tailWord_3093208).sum := by decide
  have hdescent : baseEnd_3093208 < baseStart_3093208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093221 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 5]
def baseStart_3093221 : Nat := 118140960795 + 3093221 * 2 ^ 59
def prefixEnd_3093221 : Nat := 4983230072969 + 3 ^ 40 * 3093221 * 2
def baseEnd_3093221 : Nat := 352957587462477220513787

theorem tailTrace_3093221 : CollatzResearch.WordTrace tailWord_3093221 prefixEnd_3093221 352957587462477220513787 := by
  unfold tailWord_3093221
  simp only [CollatzResearch.WordTrace]
  refine ⟨112819038326796071933383517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75212692217864047955589011 112819038326796071933383517)
  ·
    refine ⟨42307139372548526975018819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112819038326796071933383517 42307139372548526975018819)
    ·
      refine ⟨63460709058822790462528229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42307139372548526975018819 63460709058822790462528229)
      ·
        refine ⟨11898882948529273211724043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63460709058822790462528229 11898882948529273211724043)
        ·
          refine ⟨17848324422793909817586065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898882948529273211724043 17848324422793909817586065)
          ·
            refine ⟨13386243317095432363189549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17848324422793909817586065 13386243317095432363189549)
            ·
              refine ⟨5019841243910787136196081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13386243317095432363189549 5019841243910787136196081)
              ·
                refine ⟨3764880932933090352147061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5019841243910787136196081 3764880932933090352147061)
                ·
                  refine ⟨352957587462477220513787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3764880932933090352147061 352957587462477220513787)
                  ·
                    rfl

theorem cell22_3093221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_3093221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093221 prefixEnd_3093221 := by exact prefixLift 3093221
  have htrace : WordTrace (prefixWord ++ tailWord_3093221) baseStart_3093221 baseEnd_3093221 := by
    simpa [prefixWord, tailWord_3093221, baseEnd_3093221] using wordTrace_append hprefix tailTrace_3093221
  have hstable : (prefixWord ++ tailWord_3093221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093221).length < 2 ^ (prefixWord ++ tailWord_3093221).sum := by decide
  have hdescent : baseEnd_3093221 < baseStart_3093221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093238 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 5]
def baseStart_3093238 : Nat := 118140960795 + 3093238 * 2 ^ 59
def prefixEnd_3093238 : Nat := 4983230072969 + 3 ^ 40 * 3093238 * 2
def baseEnd_3093238 : Nat := 352959527278283094622103

theorem tailTrace_3093238 : CollatzResearch.WordTrace tailWord_3093238 prefixEnd_3093238 352959527278283094622103 := by
  unfold tailWord_3093238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051228647983405239797023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75213105578489655891168245 7051228647983405239797023)
  ·
    refine ⟨10576842971975107859695535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7051228647983405239797023 10576842971975107859695535)
    ·
      refine ⟨15865264457962661789543303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10576842971975107859695535 15865264457962661789543303)
      ·
        refine ⟨23797896686943992684314955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15865264457962661789543303 23797896686943992684314955)
        ·
          refine ⟨35696845030415989026472433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23797896686943992684314955 35696845030415989026472433)
          ·
            refine ⟨26772633772811991769854325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35696845030415989026472433 26772633772811991769854325)
            ·
              refine ⟨2509934416201124228423843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26772633772811991769854325 2509934416201124228423843)
              ·
                refine ⟨3764901624301686342635765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2509934416201124228423843 3764901624301686342635765)
                ·
                  refine ⟨352959527278283094622103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3764901624301686342635765 352959527278283094622103)
                  ·
                    rfl

theorem cell22_3093238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_3093238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093238 prefixEnd_3093238 := by exact prefixLift 3093238
  have htrace : WordTrace (prefixWord ++ tailWord_3093238) baseStart_3093238 baseEnd_3093238 := by
    simpa [prefixWord, tailWord_3093238, baseEnd_3093238] using wordTrace_append hprefix tailTrace_3093238
  have hstable : (prefixWord ++ tailWord_3093238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093238).length < 2 ^ (prefixWord ++ tailWord_3093238).sum := by decide
  have hdescent : baseEnd_3093238 < baseStart_3093238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093281 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_3093281 : Nat := 118140960795 + 3093281 * 2 ^ 59
def prefixEnd_3093281 : Nat := 4983230072969 + 3 ^ 40 * 3093281 * 2
def baseEnd_3093281 : Nat := 1058893301613611505041177

theorem tailTrace_3093281 : CollatzResearch.WordTrace tailWord_3093281 prefixEnd_3093281 1058893301613611505041177 := by
  unfold tailWord_3093281
  simp only [CollatzResearch.WordTrace]
  refine ⟨112821226706578702180567697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75214151137719134787045131 112821226706578702180567697)
  ·
    refine ⟨84615920029934026635425773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112821226706578702180567697 84615920029934026635425773)
    ·
      refine ⟨31730970011225259988284665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84615920029934026635425773 31730970011225259988284665)
      ·
        refine ⟨23798227508418944991213499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31730970011225259988284665 23798227508418944991213499)
        ·
          refine ⟨35697341262628417486820249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23798227508418944991213499 35697341262628417486820249)
          ·
            refine ⟨26773005946971313115115187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35697341262628417486820249 26773005946971313115115187)
            ·
              refine ⟨40159508920456969672672781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26773005946971313115115187 40159508920456969672672781)
              ·
                refine ⟨15059815845171363627252293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40159508920456969672672781 15059815845171363627252293)
                ·
                  refine ⟨2823715470969630680109805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15059815845171363627252293 2823715470969630680109805)
                  ·
                    refine ⟨1058893301613611505041177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823715470969630680109805 1058893301613611505041177)
                    ·
                      rfl

theorem cell22_3093281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_3093281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093281 prefixEnd_3093281 := by exact prefixLift 3093281
  have htrace : WordTrace (prefixWord ++ tailWord_3093281) baseStart_3093281 baseEnd_3093281 := by
    simpa [prefixWord, tailWord_3093281, baseEnd_3093281] using wordTrace_append hprefix tailTrace_3093281
  have hstable : (prefixWord ++ tailWord_3093281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093281).length < 2 ^ (prefixWord ++ tailWord_3093281).sum := by decide
  have hdescent : baseEnd_3093281 < baseStart_3093281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093298 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_3093298 : Nat := 118140960795 + 3093298 * 2 ^ 59
def prefixEnd_3093298 : Nat := 4983230072969 + 3 ^ 40 * 3093298 * 2
def baseEnd_3093298 : Nat := 1058899121061029127366125

theorem tailTrace_3093298 : CollatzResearch.WordTrace tailWord_3093298 prefixEnd_3093298 1058899121061029127366125 := by
  unfold tailWord_3093298
  simp only [CollatzResearch.WordTrace]
  refine ⟨28205461686879278520984137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75214564498344742722624365 28205461686879278520984137)
  ·
    refine ⟨21154096265159458890738103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28205461686879278520984137 21154096265159458890738103)
    ·
      refine ⟨31731144397739188336107155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21154096265159458890738103 31731144397739188336107155)
      ·
        refine ⟨47596716596608782504160733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31731144397739188336107155 47596716596608782504160733)
        ·
          refine ⟨17848768723728293439060275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47596716596608782504160733 17848768723728293439060275)
          ·
            refine ⟨26773153085592440158590413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17848768723728293439060275 26773153085592440158590413)
            ·
              refine ⟨10039932407097165059471405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26773153085592440158590413 10039932407097165059471405)
              ·
                refine ⟨3764974652661436897301777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10039932407097165059471405 3764974652661436897301777)
                ·
                  refine ⟨2823730989496077672976333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3764974652661436897301777 2823730989496077672976333)
                  ·
                    refine ⟨1058899121061029127366125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823730989496077672976333 1058899121061029127366125)
                    ·
                      rfl

theorem cell22_3093298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_3093298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093298 prefixEnd_3093298 := by exact prefixLift 3093298
  have htrace : WordTrace (prefixWord ++ tailWord_3093298) baseStart_3093298 baseEnd_3093298 := by
    simpa [prefixWord, tailWord_3093298, baseEnd_3093298] using wordTrace_append hprefix tailTrace_3093298
  have hstable : (prefixWord ++ tailWord_3093298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093298).length < 2 ^ (prefixWord ++ tailWord_3093298).sum := by decide
  have hdescent : baseEnd_3093298 < baseStart_3093298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093302 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3093302 : Nat := 118140960795 + 3093302 * 2 ^ 59
def prefixEnd_3093302 : Nat := 4983230072969 + 3 ^ 40 * 3093302 * 2
def baseEnd_3093302 : Nat := 1058900490342774450266113

theorem tailTrace_3093302 : CollatzResearch.WordTrace tailWord_3093302 prefixEnd_3093302 1058900490342774450266113 := by
  unfold tailWord_3093302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051374539968913922942635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75214661759668415178054773 7051374539968913922942635)
  ·
    refine ⟨10577061809953370884413953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7051374539968913922942635 10577061809953370884413953)
    ·
      refine ⟨7932796357465028163310465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10577061809953370884413953 7932796357465028163310465)
      ·
        refine ⟨5949597268098771122482849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7932796357465028163310465 5949597268098771122482849)
        ·
          refine ⟨4462197951074078341862137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5949597268098771122482849 4462197951074078341862137)
          ·
            refine ⟨3346648463305558756396603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4462197951074078341862137 3346648463305558756396603)
            ·
              refine ⟨5019972694958338134594905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346648463305558756396603 5019972694958338134594905)
              ·
                refine ⟨3764979521218753600946179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5019972694958338134594905 3764979521218753600946179)
                ·
                  refine ⟨5647469281828130401419269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3764979521218753600946179 5647469281828130401419269)
                  ·
                    refine ⟨1058900490342774450266113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5647469281828130401419269 1058900490342774450266113)
                    ·
                      rfl

theorem cell22_3093302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3093302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093302 prefixEnd_3093302 := by exact prefixLift 3093302
  have htrace : WordTrace (prefixWord ++ tailWord_3093302) baseStart_3093302 baseEnd_3093302 := by
    simpa [prefixWord, tailWord_3093302, baseEnd_3093302] using wordTrace_append hprefix tailTrace_3093302
  have hstable : (prefixWord ++ tailWord_3093302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093302).length < 2 ^ (prefixWord ++ tailWord_3093302).sum := by decide
  have hdescent : baseEnd_3093302 < baseStart_3093302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093356 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_3093356 : Nat := 118140960795 + 3093356 * 2 ^ 59
def prefixEnd_3093356 : Nat := 4983230072969 + 3 ^ 40 * 3093356 * 2
def baseEnd_3093356 : Nat := 352972991882112103138649

theorem tailTrace_3093356 : CollatzResearch.WordTrace tailWord_3093356 prefixEnd_3093356 352972991882112103138649 := by
  unfold tailWord_3093356
  simp only [CollatzResearch.WordTrace]
  refine ⟨56411981090653494994773961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75215974787537993326365281 56411981090653494994773961)
  ·
    refine ⟨42308985817990121246080471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56411981090653494994773961 42308985817990121246080471)
    ·
      refine ⟨63463478726985181869120707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42308985817990121246080471 63463478726985181869120707)
      ·
        refine ⟨95195218090477772803681061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63463478726985181869120707 95195218090477772803681061)
        ·
          refine ⟨17849103391964582400690199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95195218090477772803681061 17849103391964582400690199)
          ·
            refine ⟨26773655087946873601035299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17849103391964582400690199 26773655087946873601035299)
            ·
              refine ⟨40160482631920310401552949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26773655087946873601035299 40160482631920310401552949)
              ·
                refine ⟨3765045246742529100145589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40160482631920310401552949 3765045246742529100145589)
                ·
                  refine ⟨352972991882112103138649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3765045246742529100145589 352972991882112103138649)
                  ·
                    rfl

theorem cell22_3093356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_3093356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093356 prefixEnd_3093356 := by exact prefixLift 3093356
  have htrace : WordTrace (prefixWord ++ tailWord_3093356) baseStart_3093356 baseEnd_3093356 := by
    simpa [prefixWord, tailWord_3093356, baseEnd_3093356] using wordTrace_append hprefix tailTrace_3093356
  have hstable : (prefixWord ++ tailWord_3093356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093356).length < 2 ^ (prefixWord ++ tailWord_3093356).sum := by decide
  have hdescent : baseEnd_3093356 < baseStart_3093356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093431 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 1, 6]
def baseStart_3093431 : Nat := 118140960795 + 3093431 * 2 ^ 59
def prefixEnd_3093431 : Nat := 4983230072969 + 3 ^ 40 * 3093431 * 2
def baseEnd_3093431 : Nat := 1058944649679061113790717

theorem tailTrace_3093431 : CollatzResearch.WordTrace tailWord_3093431 prefixEnd_3093431 1058944649679061113790717 := by
  unfold tailWord_3093431
  simp only [CollatzResearch.WordTrace]
  refine ⟨112826697656035277798528147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75217798437356851865685431 112826697656035277798528147)
  ·
    refine ⟨169240046484052916697792221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112826697656035277798528147 169240046484052916697792221)
    ·
      refine ⟨63465017431519843761672083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169240046484052916697792221 63465017431519843761672083)
      ·
        refine ⟨95197526147279765642508125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63465017431519843761672083 95197526147279765642508125)
        ·
          refine ⟨35699072305229912115940547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95197526147279765642508125 35699072305229912115940547)
          ·
            refine ⟨53548608457844868173910821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35699072305229912115940547 53548608457844868173910821)
            ·
              refine ⟨10040364085845912782608279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53548608457844868173910821 10040364085845912782608279)
              ·
                refine ⟨15060546128768869173912419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10040364085845912782608279 15060546128768869173912419)
                ·
                  refine ⟨22590819193153303760868629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15060546128768869173912419 22590819193153303760868629)
                  ·
                    refine ⟨1058944649679061113790717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22590819193153303760868629 1058944649679061113790717)
                    ·
                      rfl

theorem cell22_3093431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_3093431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093431 prefixEnd_3093431 := by exact prefixLift 3093431
  have htrace : WordTrace (prefixWord ++ tailWord_3093431) baseStart_3093431 baseEnd_3093431 := by
    simpa [prefixWord, tailWord_3093431, baseEnd_3093431] using wordTrace_append hprefix tailTrace_3093431
  have hstable : (prefixWord ++ tailWord_3093431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093431).length < 2 ^ (prefixWord ++ tailWord_3093431).sum := by decide
  have hdescent : baseEnd_3093431 < baseStart_3093431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093433 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_3093433 : Nat := 118140960795 + 3093433 * 2 ^ 59
def prefixEnd_3093433 : Nat := 4983230072969 + 3 ^ 40 * 3093433 * 2
def baseEnd_3093433 : Nat := 1058945334319933775240711

theorem tailTrace_3093433 : CollatzResearch.WordTrace tailWord_3093433 prefixEnd_3093433 1058945334319933775240711 := by
  unfold tailWord_3093433
  simp only [CollatzResearch.WordTrace]
  refine ⟨112826770602028032140100953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75217847068018688093400635 112826770602028032140100953)
  ·
    refine ⟨84620077951521024105075715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112826770602028032140100953 84620077951521024105075715)
    ·
      refine ⟨126930116927281536157613573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84620077951521024105075715 126930116927281536157613573)
      ·
        refine ⟨23799396923865288029552545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126930116927281536157613573 23799396923865288029552545)
        ·
          refine ⟨17849547692898966022164409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23799396923865288029552545 17849547692898966022164409)
          ·
            refine ⟨13387160769674224516623307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17849547692898966022164409 13387160769674224516623307)
            ·
              refine ⟨20080741154511336774934961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13387160769674224516623307 20080741154511336774934961)
              ·
                refine ⟨15060555865883502581201221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20080741154511336774934961 15060555865883502581201221)
                ·
                  refine ⟨2823854224853156733975229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15060555865883502581201221 2823854224853156733975229)
                  ·
                    refine ⟨1058945334319933775240711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823854224853156733975229 1058945334319933775240711)
                    ·
                      rfl

theorem cell22_3093433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_3093433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093433 prefixEnd_3093433 := by exact prefixLift 3093433
  have htrace : WordTrace (prefixWord ++ tailWord_3093433) baseStart_3093433 baseEnd_3093433 := by
    simpa [prefixWord, tailWord_3093433, baseEnd_3093433] using wordTrace_append hprefix tailTrace_3093433
  have hstable : (prefixWord ++ tailWord_3093433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093433).length < 2 ^ (prefixWord ++ tailWord_3093433).sum := by decide
  have hdescent : baseEnd_3093433 < baseStart_3093433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093476 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3093476 : Nat := 118140960795 + 3093476 * 2 ^ 59
def prefixEnd_3093476 : Nat := 4983230072969 + 3 ^ 40 * 3093476 * 2
def baseEnd_3093476 : Nat := 1058960054098695996415579

theorem tailTrace_3093476 : CollatzResearch.WordTrace tailWord_3093476 prefixEnd_3093476 1058960054098695996415579 := by
  unfold tailWord_3093476
  simp only [CollatzResearch.WordTrace]
  refine ⟨56414169470436125241958141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75218892627248166989277521 56414169470436125241958141)
  ·
    refine ⟨21155313551413546965734303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56414169470436125241958141 21155313551413546965734303)
    ·
      refine ⟨31732970327120320448601455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21155313551413546965734303 31732970327120320448601455)
      ·
        refine ⟨47599455490680480672902183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31732970327120320448601455 47599455490680480672902183)
        ·
          refine ⟨71399183236020721009353275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47599455490680480672902183 71399183236020721009353275)
          ·
            refine ⟨107098774854031081514029913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71399183236020721009353275 107098774854031081514029913)
            ·
              refine ⟨80324081140523311135522435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107098774854031081514029913 80324081140523311135522435)
              ·
                refine ⟨120486121710784966703283653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80324081140523311135522435 120486121710784966703283653)
                ·
                  refine ⟨22591147820772181256865685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 120486121710784966703283653 22591147820772181256865685)
                  ·
                    refine ⟨1058960054098695996415579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22591147820772181256865685 1058960054098695996415579)
                    ·
                      rfl

theorem cell22_3093476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3093476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093476 prefixEnd_3093476 := by exact prefixLift 3093476
  have htrace : WordTrace (prefixWord ++ tailWord_3093476) baseStart_3093476 baseEnd_3093476 := by
    simpa [prefixWord, tailWord_3093476, baseEnd_3093476] using wordTrace_append hprefix tailTrace_3093476
  have hstable : (prefixWord ++ tailWord_3093476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093476).length < 2 ^ (prefixWord ++ tailWord_3093476).sum := by decide
  have hdescent : baseEnd_3093476 < baseStart_3093476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093512 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 1, 3]
def baseStart_3093512 : Nat := 118140960795 + 3093512 * 2 ^ 59
def prefixEnd_3093512 : Nat := 4983230072969 + 3 ^ 40 * 3093512 * 2
def baseEnd_3093512 : Nat := 1058972377634403902515469

theorem tailTrace_3093512 : CollatzResearch.WordTrace tailWord_3093512 prefixEnd_3093512 1058972377634403902515469 := by
  unfold tailWord_3093512
  simp only [CollatzResearch.WordTrace]
  refine ⟨56414825984370914316113395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75219767979161219088151193 56414825984370914316113395)
  ·
    refine ⟨84622238976556371474170093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56414825984370914316113395 84622238976556371474170093)
    ·
      refine ⟨31733339616208639302813785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84622238976556371474170093 31733339616208639302813785)
      ·
        refine ⟨23800004712156479477110339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31733339616208639302813785 23800004712156479477110339)
        ·
          refine ⟨35700007068234719215665509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23800004712156479477110339 35700007068234719215665509)
          ·
            refine ⟨6693751325294009852937283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35700007068234719215665509 6693751325294009852937283)
            ·
              refine ⟨10040626987941014779405925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6693751325294009852937283 10040626987941014779405925)
              ·
                refine ⟨1882617560238940271138611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10040626987941014779405925 1882617560238940271138611)
                ·
                  refine ⟨2823926340358410406707917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882617560238940271138611 2823926340358410406707917)
                  ·
                    refine ⟨1058972377634403902515469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823926340358410406707917 1058972377634403902515469)
                    ·
                      rfl

theorem cell22_3093512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_3093512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093512 prefixEnd_3093512 := by exact prefixLift 3093512
  have htrace : WordTrace (prefixWord ++ tailWord_3093512) baseStart_3093512 baseEnd_3093512 := by
    simpa [prefixWord, tailWord_3093512, baseEnd_3093512] using wordTrace_append hprefix tailTrace_3093512
  have hstable : (prefixWord ++ tailWord_3093512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093512).length < 2 ^ (prefixWord ++ tailWord_3093512).sum := by decide
  have hdescent : baseEnd_3093512 < baseStart_3093512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093551 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_3093551 : Nat := 118140960795 + 3093551 * 2 ^ 59
def prefixEnd_3093551 : Nat := 4983230072969 + 3 ^ 40 * 3093551 * 2
def baseEnd_3093551 : Nat := 1058985728131420800790349

theorem tailTrace_3093551 : CollatzResearch.WordTrace tailWord_3093551 prefixEnd_3093551 1058985728131420800790349 := by
  unfold tailWord_3093551
  simp only [CollatzResearch.WordTrace]
  refine ⟨112831074415600538292896507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75220716277067025528597671 112831074415600538292896507)
  ·
    refine ⟨169246611623400807439344761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112831074415600538292896507 169246611623400807439344761)
    ·
      refine ⟨126934958717550605579508571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169246611623400807439344761 126934958717550605579508571)
      ·
        refine ⟨190402438076325908369262857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126934958717550605579508571 190402438076325908369262857)
        ·
          refine ⟨142801828557244431276947143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 190402438076325908369262857 142801828557244431276947143)
          ·
            refine ⟨214202742835866646915420715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142801828557244431276947143 214202742835866646915420715)
            ·
              refine ⟨321304114253799970373131073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214202742835866646915420715 321304114253799970373131073)
              ·
                refine ⟨240978085690349977779848305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321304114253799970373131073 240978085690349977779848305)
                ·
                  refine ⟨180733564267762483334886229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240978085690349977779848305 180733564267762483334886229)
                  ·
                    refine ⟨1058985728131420800790349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 180733564267762483334886229 1058985728131420800790349)
                    ·
                      rfl

theorem cell22_3093551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_3093551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093551 prefixEnd_3093551 := by exact prefixLift 3093551
  have htrace : WordTrace (prefixWord ++ tailWord_3093551) baseStart_3093551 baseEnd_3093551 := by
    simpa [prefixWord, tailWord_3093551, baseEnd_3093551] using wordTrace_append hprefix tailTrace_3093551
  have hstable : (prefixWord ++ tailWord_3093551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093551).length < 2 ^ (prefixWord ++ tailWord_3093551).sum := by decide
  have hdescent : baseEnd_3093551 < baseStart_3093551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093585 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_3093585 : Nat := 118140960795 + 3093585 * 2 ^ 59
def prefixEnd_3093585 : Nat := 4983230072969 + 3 ^ 40 * 3093585 * 2
def baseEnd_3093585 : Nat := 1058997367026256045440245

theorem tailTrace_3093585 : CollatzResearch.WordTrace tailWord_3093585 prefixEnd_3093585 1058997367026256045440245 := by
  unfold tailWord_3093585
  simp only [CollatzResearch.WordTrace]
  refine ⟨112832314497477362099634209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75221542998318241399756139 112832314497477362099634209)
  ·
    refine ⟨84624235873108021574725657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112832314497477362099634209 84624235873108021574725657)
    ·
      refine ⟨63468176904831016181044243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84624235873108021574725657 63468176904831016181044243)
      ·
        refine ⟨95202265357246524271566365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63468176904831016181044243 95202265357246524271566365)
        ·
          refine ⟨35700849508967446601837387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95202265357246524271566365 35700849508967446601837387)
          ·
            refine ⟨53551274263451169902756081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35700849508967446601837387 53551274263451169902756081)
            ·
              refine ⟨40163455697588377427067061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53551274263451169902756081 40163455697588377427067061)
              ·
                refine ⟨3765323971648910383787537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40163455697588377427067061 3765323971648910383787537)
                ·
                  refine ⟨2823992978736682787840653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3765323971648910383787537 2823992978736682787840653)
                  ·
                    refine ⟨1058997367026256045440245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2823992978736682787840653 1058997367026256045440245)
                    ·
                      rfl

theorem cell22_3093585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_3093585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093585 prefixEnd_3093585 := by exact prefixLift 3093585
  have htrace : WordTrace (prefixWord ++ tailWord_3093585) baseStart_3093585 baseEnd_3093585 := by
    simpa [prefixWord, tailWord_3093585, baseEnd_3093585] using wordTrace_append hprefix tailTrace_3093585
  have hstable : (prefixWord ++ tailWord_3093585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093585).length < 2 ^ (prefixWord ++ tailWord_3093585).sum := by decide
  have hdescent : baseEnd_3093585 < baseStart_3093585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093602 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3093602 : Nat := 118140960795 + 3093602 * 2 ^ 59
def prefixEnd_3093602 : Nat := 4983230072969 + 3 ^ 40 * 3093602 * 2
def baseEnd_3093602 : Nat := 1059003186473673667765193

theorem tailTrace_3093602 : CollatzResearch.WordTrace tailWord_3093602 prefixEnd_3093602 1059003186473673667765193 := by
  unfold tailWord_3093602
  simp only [CollatzResearch.WordTrace]
  refine ⟨28208233634603943500750765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75221956358943849335335373 28208233634603943500750765)
  ·
    refine ⟨10578087612976478812781537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28208233634603943500750765 10578087612976478812781537)
    ·
      refine ⟨7933565709732359109586153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10578087612976478812781537 7933565709732359109586153)
      ·
        refine ⟨5950174282299269332189615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7933565709732359109586153 5950174282299269332189615)
        ·
          refine ⟨8925261423448903998284423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950174282299269332189615 8925261423448903998284423)
          ·
            refine ⟨13387892135173355997426635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925261423448903998284423 13387892135173355997426635)
            ·
              refine ⟨20081838202760033996139953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13387892135173355997426635 20081838202760033996139953)
              ·
                refine ⟨15061378652070025497104965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20081838202760033996139953 15061378652070025497104965)
                ·
                  refine ⟨2824008497263129780707181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15061378652070025497104965 2824008497263129780707181)
                  ·
                    refine ⟨1059003186473673667765193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824008497263129780707181 1059003186473673667765193)
                    ·
                      rfl

theorem cell22_3093602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3093602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093602 prefixEnd_3093602 := by exact prefixLift 3093602
  have htrace : WordTrace (prefixWord ++ tailWord_3093602) baseStart_3093602 baseEnd_3093602 := by
    simpa [prefixWord, tailWord_3093602, baseEnd_3093602] using wordTrace_append hprefix tailTrace_3093602
  have hstable : (prefixWord ++ tailWord_3093602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093602).length < 2 ^ (prefixWord ++ tailWord_3093602).sum := by decide
  have hdescent : baseEnd_3093602 < baseStart_3093602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093621 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 4]
def baseStart_3093621 : Nat := 118140960795 + 3093621 * 2 ^ 59
def prefixEnd_3093621 : Nat := 4983230072969 + 3 ^ 40 * 3093621 * 2
def baseEnd_3093621 : Nat := 353003230187321317180045

theorem tailTrace_3093621 : CollatzResearch.WordTrace tailWord_3093621 prefixEnd_3093621 353003230187321317180045 := by
  unfold tailWord_3093621
  simp only [CollatzResearch.WordTrace]
  refine ⟨112833627525346940247944717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75222418350231293498629811 112833627525346940247944717)
  ·
    refine ⟨42312610322005102592979269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112833627525346940247944717 42312610322005102592979269)
    ·
      refine ⟨7933614435375956736183613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42312610322005102592979269 7933614435375956736183613)
      ·
        refine ⟨2975105413265983776068855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7933614435375956736183613 2975105413265983776068855)
        ·
          refine ⟨4462658119898975664103283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975105413265983776068855 4462658119898975664103283)
          ·
            refine ⟨6693987179848463496154925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4462658119898975664103283 6693987179848463496154925)
            ·
              refine ⟨2510245192443173811058097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6693987179848463496154925 2510245192443173811058097)
              ·
                refine ⟨1882683894332380358293573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510245192443173811058097 1882683894332380358293573)
                ·
                  refine ⟨353003230187321317180045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882683894332380358293573 353003230187321317180045)
                  ·
                    rfl

theorem cell22_3093621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_3093621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093621 prefixEnd_3093621 := by exact prefixLift 3093621
  have htrace : WordTrace (prefixWord ++ tailWord_3093621) baseStart_3093621 baseEnd_3093621 := by
    simpa [prefixWord, tailWord_3093621, baseEnd_3093621] using wordTrace_append hprefix tailTrace_3093621
  have hstable : (prefixWord ++ tailWord_3093621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093621).length < 2 ^ (prefixWord ++ tailWord_3093621).sum := by decide
  have hdescent : baseEnd_3093621 < baseStart_3093621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093628 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_3093628 : Nat := 118140960795 + 3093628 * 2 ^ 59
def prefixEnd_3093628 : Nat := 4983230072969 + 3 ^ 40 * 3093628 * 2
def baseEnd_3093628 : Nat := 1059012086805018266615113

theorem tailTrace_3093628 : CollatzResearch.WordTrace tailWord_3093628 prefixEnd_3093628 1059012086805018266615113 := by
  unfold tailWord_3093628
  simp only [CollatzResearch.WordTrace]
  refine ⟨56416941418160790221724769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75222588557547720295633025 56416941418160790221724769)
  ·
    refine ⟨42312706063620592666293577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56416941418160790221724769 42312706063620592666293577)
    ·
      refine ⟨31734529547715444499720183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42312706063620592666293577 31734529547715444499720183)
      ·
        refine ⟨47601794321573166749580275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31734529547715444499720183 47601794321573166749580275)
        ·
          refine ⟨71402691482359750124370413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47601794321573166749580275 71402691482359750124370413)
          ·
            refine ⟨26776009305884906296638905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71402691482359750124370413 26776009305884906296638905)
            ·
              refine ⟨20082006979413679722479179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26776009305884906296638905 20082006979413679722479179)
              ·
                refine ⟨30123010469120519583718769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20082006979413679722479179 30123010469120519583718769)
                ·
                  refine ⟨22592257851840389687789077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30123010469120519583718769 22592257851840389687789077)
                  ·
                    refine ⟨1059012086805018266615113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22592257851840389687789077 1059012086805018266615113)
                    ·
                      rfl

theorem cell22_3093628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_3093628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093628 prefixEnd_3093628 := by exact prefixLift 3093628
  have htrace : WordTrace (prefixWord ++ tailWord_3093628) baseStart_3093628 baseEnd_3093628 := by
    simpa [prefixWord, tailWord_3093628, baseEnd_3093628] using wordTrace_append hprefix tailTrace_3093628
  have hstable : (prefixWord ++ tailWord_3093628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093628).length < 2 ^ (prefixWord ++ tailWord_3093628).sum := by decide
  have hdescent : baseEnd_3093628 < baseStart_3093628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093681 : List Nat := [1, 2, 2, 5, 1, 1, 4, 2, 1, 3]
def baseStart_3093681 : Nat := 118140960795 + 3093681 * 2 ^ 59
def prefixEnd_3093681 : Nat := 4983230072969 + 3 ^ 40 * 3093681 * 2
def baseEnd_3093681 : Nat := 1059030229788143795039951

theorem tailTrace_3093681 : CollatzResearch.WordTrace tailWord_3093681 prefixEnd_3093681 1059030229788143795039951 := by
  unfold tailWord_3093681
  simp only [CollatzResearch.WordTrace]
  refine ⟨112835815905129570495128897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75223877270086380330085931 112835815905129570495128897)
  ·
    refine ⟨84626861928847177871346673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112835815905129570495128897 84626861928847177871346673)
    ·
      refine ⟨63470146446635383403510005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84626861928847177871346673 63470146446635383403510005)
      ·
        refine ⟨5950326229372067194079063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63470146446635383403510005 5950326229372067194079063)
        ·
          refine ⟨8925489344058100791118595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5950326229372067194079063 8925489344058100791118595)
          ·
            refine ⟨13388234016087151186677893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8925489344058100791118595 13388234016087151186677893)
            ·
              refine ⟨2510293878016340847502105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13388234016087151186677893 2510293878016340847502105)
              ·
                refine ⟨1882720408512255635626579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510293878016340847502105 1882720408512255635626579)
                ·
                  refine ⟨2824080612768383453439869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882720408512255635626579 2824080612768383453439869)
                  ·
                    refine ⟨1059030229788143795039951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824080612768383453439869 1059030229788143795039951)
                    ·
                      rfl

theorem cell22_3093681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_3093681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093681 prefixEnd_3093681 := by exact prefixLift 3093681
  have htrace : WordTrace (prefixWord ++ tailWord_3093681) baseStart_3093681 baseEnd_3093681 := by
    simpa [prefixWord, tailWord_3093681, baseEnd_3093681] using wordTrace_append hprefix tailTrace_3093681
  have hstable : (prefixWord ++ tailWord_3093681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093681).length < 2 ^ (prefixWord ++ tailWord_3093681).sum := by decide
  have hdescent : baseEnd_3093681 < baseStart_3093681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093750 : List Nat := [5, 1, 1, 1, 1, 1, 1, 11]
def baseStart_3093750 : Nat := 118140960795 + 3093750 * 2 ^ 59
def prefixEnd_3093750 : Nat := 4983230072969 + 3 ^ 40 * 3093750 * 2
def baseEnd_3093750 : Nat := 117672649988694512784971

theorem tailTrace_3093750 : CollatzResearch.WordTrace tailWord_3093750 prefixEnd_3093750 117672649988694512784971 := by
  unfold tailWord_3093750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7052395783867474704961919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75225555027919730186260469 7052395783867474704961919)
  ·
    refine ⟨10578593675801212057442879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7052395783867474704961919 10578593675801212057442879)
    ·
      refine ⟨15867890513701818086164319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10578593675801212057442879 15867890513701818086164319)
      ·
        refine ⟨23801835770552727129246479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15867890513701818086164319 23801835770552727129246479)
        ·
          refine ⟨35702753655829090693869719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23801835770552727129246479 35702753655829090693869719)
          ·
            refine ⟨53554130483743636040804579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35702753655829090693869719 53554130483743636040804579)
            ·
              refine ⟨80331195725615454061206869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53554130483743636040804579 80331195725615454061206869)
              ·
                refine ⟨117672649988694512784971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80331195725615454061206869 117672649988694512784971)
                ·
                  rfl

theorem cell22_3093750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_3093750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093750 prefixEnd_3093750 := by exact prefixLift 3093750
  have htrace : WordTrace (prefixWord ++ tailWord_3093750) baseStart_3093750 baseEnd_3093750 := by
    simpa [prefixWord, tailWord_3093750, baseEnd_3093750] using wordTrace_append hprefix tailTrace_3093750
  have hstable : (prefixWord ++ tailWord_3093750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093750).length < 2 ^ (prefixWord ++ tailWord_3093750).sum := by decide
  have hdescent : baseEnd_3093750 < baseStart_3093750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093754 : List Nat := [3, 1, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_3093754 : Nat := 118140960795 + 3093754 * 2 ^ 59
def prefixEnd_3093754 : Nat := 4983230072969 + 3 ^ 40 * 3093754 * 2
def baseEnd_3093754 : Nat := 1059055219179995937964727

theorem tailTrace_3093754 : CollatzResearch.WordTrace tailWord_3093754 prefixEnd_3093754 1059055219179995937964727 := by
  unfold tailWord_3093754
  simp only [CollatzResearch.WordTrace]
  refine ⟨28209619608466275990634079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75225652289243402641690877 28209619608466275990634079)
  ·
    refine ⟨42314429412699413985951119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28209619608466275990634079 42314429412699413985951119)
    ·
      refine ⟨63471644119049120978926679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42314429412699413985951119 63471644119049120978926679)
      ·
        refine ⟨95207466178573681468390019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63471644119049120978926679 95207466178573681468390019)
        ·
          refine ⟨142811199267860522202585029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95207466178573681468390019 142811199267860522202585029)
          ·
            refine ⟨26777099862723847912984693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 142811199267860522202585029 26777099862723847912984693)
            ·
              refine ⟨2510353112130360741842315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26777099862723847912984693 2510353112130360741842315)
              ·
                refine ⟨3765529668195541112763473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510353112130360741842315 3765529668195541112763473)
                ·
                  refine ⟨2824147251146655834572605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3765529668195541112763473 2824147251146655834572605)
                  ·
                    refine ⟨1059055219179995937964727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824147251146655834572605 1059055219179995937964727)
                    ·
                      rfl

theorem cell22_3093754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_3093754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093754 prefixEnd_3093754 := by exact prefixLift 3093754
  have htrace : WordTrace (prefixWord ++ tailWord_3093754) baseStart_3093754 baseEnd_3093754 := by
    simpa [prefixWord, tailWord_3093754, baseEnd_3093754] using wordTrace_append hprefix tailTrace_3093754
  have hstable : (prefixWord ++ tailWord_3093754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093754).length < 2 ^ (prefixWord ++ tailWord_3093754).sum := by decide
  have hdescent : baseEnd_3093754 < baseStart_3093754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093795 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 7]
def baseStart_3093795 : Nat := 118140960795 + 3093795 * 2 ^ 59
def prefixEnd_3093795 : Nat := 4983230072969 + 3 ^ 40 * 3093795 * 2
def baseEnd_3093795 : Nat := 353023084772628499229867

theorem tailTrace_3093795 : CollatzResearch.WordTrace tailWord_3093795 prefixEnd_3093795 353023084772628499229867 := by
  unfold tailWord_3093795
  simp only [CollatzResearch.WordTrace]
  refine ⟨112839973826716567964778839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75226649217811045309852559 112839973826716567964778839)
  ·
    refine ⟨169259960740074851947168259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112839973826716567964778839 169259960740074851947168259)
    ·
      refine ⟨253889941110112277920752389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169259960740074851947168259 253889941110112277920752389)
      ·
        refine ⟨47604363958146052110141073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 253889941110112277920752389 47604363958146052110141073)
        ·
          refine ⟨35703272968609539082605805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47604363958146052110141073 35703272968609539082605805)
          ·
            refine ⟨13388727363228577155977177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35703272968609539082605805 13388727363228577155977177)
            ·
              refine ⟨10041545522421432866982883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13388727363228577155977177 10041545522421432866982883)
              ·
                refine ⟨15062318283632149300474325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10041545522421432866982883 15062318283632149300474325)
                ·
                  refine ⟨353023084772628499229867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15062318283632149300474325 353023084772628499229867)
                  ·
                    rfl

theorem cell22_3093795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 7].length) (baseStart_3093795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093795 prefixEnd_3093795 := by exact prefixLift 3093795
  have htrace : WordTrace (prefixWord ++ tailWord_3093795) baseStart_3093795 baseEnd_3093795 := by
    simpa [prefixWord, tailWord_3093795, baseEnd_3093795] using wordTrace_append hprefix tailTrace_3093795
  have hstable : (prefixWord ++ tailWord_3093795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093795).length < 2 ^ (prefixWord ++ tailWord_3093795).sum := by decide
  have hdescent : baseEnd_3093795 < baseStart_3093795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093855 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 5, 5]
def baseStart_3093855 : Nat := 118140960795 + 3093855 * 2 ^ 59
def prefixEnd_3093855 : Nat := 4983230072969 + 3 ^ 40 * 3093855 * 2
def baseEnd_3093855 : Nat := 1059089793544065341189417

theorem tailTrace_3093855 : CollatzResearch.WordTrace tailWord_3093855 prefixEnd_3093855 1059089793544065341189417 := by
  unfold tailWord_3093855
  simp only [CollatzResearch.WordTrace]
  refine ⟨112842162206499198211963019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75228108137666132141308679 112842162206499198211963019)
  ·
    refine ⟨169263243309748797317944529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112842162206499198211963019 169263243309748797317944529)
    ·
      refine ⟨126947432482311597988458397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169263243309748797317944529 126947432482311597988458397)
      ·
        refine ⟨47605287180866849245671899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126947432482311597988458397 47605287180866849245671899)
        ·
          refine ⟨71407930771300273868507849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47605287180866849245671899 71407930771300273868507849)
          ·
            refine ⟨53555948078475205401380887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71407930771300273868507849 53555948078475205401380887)
            ·
              refine ⟨80333922117712808102071331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53555948078475205401380887 80333922117712808102071331)
              ·
                refine ⟨120500883176569212153106997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80333922117712808102071331 120500883176569212153106997)
                ·
                  refine ⟨11296957797803363639353781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120500883176569212153106997 11296957797803363639353781)
                  ·
                    refine ⟨1059089793544065341189417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11296957797803363639353781 1059089793544065341189417)
                    ·
                      rfl

theorem cell22_3093855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_3093855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093855 prefixEnd_3093855 := by exact prefixLift 3093855
  have htrace : WordTrace (prefixWord ++ tailWord_3093855) baseStart_3093855 baseEnd_3093855 := by
    simpa [prefixWord, tailWord_3093855, baseEnd_3093855] using wordTrace_append hprefix tailTrace_3093855
  have hstable : (prefixWord ++ tailWord_3093855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093855).length < 2 ^ (prefixWord ++ tailWord_3093855).sum := by decide
  have hdescent : baseEnd_3093855 < baseStart_3093855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093872 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_3093872 : Nat := 118140960795 + 3093872 * 2 ^ 59
def prefixEnd_3093872 : Nat := 4983230072969 + 3 ^ 40 * 3093872 * 2
def baseEnd_3093872 : Nat := 1059095612991482963514365

theorem tailTrace_3093872 : CollatzResearch.WordTrace tailWord_3093872 prefixEnd_3093872 1059095612991482963514365 := by
  unfold tailWord_3093872
  simp only [CollatzResearch.WordTrace]
  refine ⟨56421391123718805057665935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75228521498291740076887913 56421391123718805057665935)
  ·
    refine ⟨84632086685578207586498903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56421391123718805057665935 84632086685578207586498903)
    ·
      refine ⟨126948130028367311379748355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84632086685578207586498903 126948130028367311379748355)
      ·
        refine ⟨190422195042550967069622533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126948130028367311379748355 190422195042550967069622533)
        ·
          refine ⟨35704161570478306325554225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190422195042550967069622533 35704161570478306325554225)
          ·
            refine ⟨26778121177858729744165669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35704161570478306325554225 26778121177858729744165669)
            ·
              refine ⟨5020897720848511827031063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26778121177858729744165669 5020897720848511827031063)
              ·
                refine ⟨7531346581272767740546595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5020897720848511827031063 7531346581272767740546595)
                ·
                  refine ⟨11297019871909151610819893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7531346581272767740546595 11297019871909151610819893)
                  ·
                    refine ⟨1059095612991482963514365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11297019871909151610819893 1059095612991482963514365)
                    ·
                      rfl

theorem cell22_3093872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_3093872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093872 prefixEnd_3093872 := by exact prefixLift 3093872
  have htrace : WordTrace (prefixWord ++ tailWord_3093872) baseStart_3093872 baseEnd_3093872 := by
    simpa [prefixWord, tailWord_3093872, baseEnd_3093872] using wordTrace_append hprefix tailTrace_3093872
  have hstable : (prefixWord ++ tailWord_3093872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093872).length < 2 ^ (prefixWord ++ tailWord_3093872).sum := by decide
  have hdescent : baseEnd_3093872 < baseStart_3093872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093981 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3093981 : Nat := 118140960795 + 3093981 * 2 ^ 59
def prefixEnd_3093981 : Nat := 4983230072969 + 3 ^ 40 * 3093981 * 2
def baseEnd_3093981 : Nat := 353044308639681004179677

theorem tailTrace_3093981 : CollatzResearch.WordTrace tailWord_3093981 prefixEnd_3093981 353044308639681004179677 := by
  unfold tailWord_3093981
  simp only [CollatzResearch.WordTrace]
  refine ⟨112846757804042721731049797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75231171869361814487366531 112846757804042721731049797)
  ·
    refine ⟨21158767088258010324571837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112846757804042721731049797 21158767088258010324571837)
    ·
      refine ⟨7934537658096753871714439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21158767088258010324571837 7934537658096753871714439)
      ·
        refine ⟨11901806487145130807571659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7934537658096753871714439 11901806487145130807571659)
        ·
          refine ⟨17852709730717696211357489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11901806487145130807571659 17852709730717696211357489)
          ·
            refine ⟨13389532298038272158518117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17852709730717696211357489 13389532298038272158518117)
            ·
              refine ⟨2510537305882176029722147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13389532298038272158518117 2510537305882176029722147)
              ·
                refine ⟨3765805958823264044583221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510537305882176029722147 3765805958823264044583221)
                ·
                  refine ⟨353044308639681004179677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3765805958823264044583221 353044308639681004179677)
                  ·
                    rfl

theorem cell22_3093981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3093981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093981 prefixEnd_3093981 := by exact prefixLift 3093981
  have htrace : WordTrace (prefixWord ++ tailWord_3093981) baseStart_3093981 baseEnd_3093981 := by
    simpa [prefixWord, tailWord_3093981, baseEnd_3093981] using wordTrace_append hprefix tailTrace_3093981
  have hstable : (prefixWord ++ tailWord_3093981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093981).length < 2 ^ (prefixWord ++ tailWord_3093981).sum := by decide
  have hdescent : baseEnd_3093981 < baseStart_3093981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3093992 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_3093992 : Nat := 118140960795 + 3093992 * 2 ^ 59
def prefixEnd_3093992 : Nat := 4983230072969 + 3 ^ 40 * 3093992 * 2
def baseEnd_3093992 : Nat := 353045563814614216837999

theorem tailTrace_3093992 : CollatzResearch.WordTrace tailWord_3093992 prefixEnd_3093992 353045563814614216837999 := by
  unfold tailWord_3093992
  simp only [CollatzResearch.WordTrace]
  refine ⟨56423579503501435304850115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75231439338001913739800153 56423579503501435304850115)
  ·
    refine ⟨84635369255252152957275173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56423579503501435304850115 84635369255252152957275173)
    ·
      refine ⟨15869131735359778679489095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84635369255252152957275173 15869131735359778679489095)
      ·
        refine ⟨23803697603039668019233643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15869131735359778679489095 23803697603039668019233643)
        ·
          refine ⟨35705546404559502028850465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23803697603039668019233643 35705546404559502028850465)
          ·
            refine ⟨26779159803419626521637849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35705546404559502028850465 26779159803419626521637849)
            ·
              refine ⟨20084369852564719891228387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26779159803419626521637849 20084369852564719891228387)
              ·
                refine ⟨30126554778847079836842581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20084369852564719891228387 30126554778847079836842581)
                ·
                  refine ⟨353045563814614216837999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30126554778847079836842581 353045563814614216837999)
                  ·
                    rfl

theorem cell22_3093992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_3093992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3093992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3093992 prefixEnd_3093992 := by exact prefixLift 3093992
  have htrace : WordTrace (prefixWord ++ tailWord_3093992) baseStart_3093992 baseEnd_3093992 := by
    simpa [prefixWord, tailWord_3093992, baseEnd_3093992] using wordTrace_append hprefix tailTrace_3093992
  have hstable : (prefixWord ++ tailWord_3093992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3093992).length < 2 ^ (prefixWord ++ tailWord_3093992).sum := by decide
  have hdescent : baseEnd_3093992 < baseStart_3093992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3093992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094009 : List Nat := [1, 2, 1, 3, 1, 2, 1, 7, 4]
def baseStart_3094009 : Nat := 118140960795 + 3094009 * 2 ^ 59
def prefixEnd_3094009 : Nat := 4983230072969 + 3 ^ 40 * 3094009 * 2
def baseEnd_3094009 : Nat := 353047503630420090946315

theorem tailTrace_3094009 : CollatzResearch.WordTrace tailWord_3094009 prefixEnd_3094009 353047503630420090946315 := by
  unfold tailWord_3094009
  simp only [CollatzResearch.WordTrace]
  refine ⟨112847779047941282513069081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75231852698627521675379387 112847779047941282513069081)
  ·
    refine ⟨84635834285955961884801811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112847779047941282513069081 84635834285955961884801811)
    ·
      refine ⟨126953751428933942827202717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84635834285955961884801811 126953751428933942827202717)
      ·
        refine ⟨47607656785850228560201019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126953751428933942827202717 47607656785850228560201019)
        ·
          refine ⟨71411485178775342840301529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47607656785850228560201019 71411485178775342840301529)
          ·
            refine ⟨53558613884081507130226147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71411485178775342840301529 53558613884081507130226147)
            ·
              refine ⟨80337920826122260695339221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53558613884081507130226147 80337920826122260695339221)
              ·
                refine ⟨1882920019362240485047013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80337920826122260695339221 1882920019362240485047013)
                ·
                  refine ⟨353047503630420090946315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882920019362240485047013 353047503630420090946315)
                  ·
                    rfl

theorem cell22_3094009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 7, 4].length) (baseStart_3094009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094009 prefixEnd_3094009 := by exact prefixLift 3094009
  have htrace : WordTrace (prefixWord ++ tailWord_3094009) baseStart_3094009 baseEnd_3094009 := by
    simpa [prefixWord, tailWord_3094009, baseEnd_3094009] using wordTrace_append hprefix tailTrace_3094009
  have hstable : (prefixWord ++ tailWord_3094009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094009).length < 2 ^ (prefixWord ++ tailWord_3094009).sum := by decide
  have hdescent : baseEnd_3094009 < baseStart_3094009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094024 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_3094024 : Nat := 118140960795 + 3094024 * 2 ^ 59
def prefixEnd_3094024 : Nat := 4983230072969 + 3 ^ 40 * 3094024 * 2
def baseEnd_3094024 : Nat := 1059147645697805233713899

theorem tailTrace_3094024 : CollatzResearch.WordTrace tailWord_3094024 prefixEnd_3094024 1059147645697805233713899 := by
  unfold tailWord_3094024
  simp only [CollatzResearch.WordTrace]
  refine ⟨56424163071443470037432563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75232217428591293383243417 56424163071443470037432563)
  ·
    refine ⟨84636244607165205056148845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56424163071443470037432563 84636244607165205056148845)
    ·
      refine ⟨31738591727686951896055817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84636244607165205056148845 31738591727686951896055817)
      ·
        refine ⟨23803943795765213922041863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31738591727686951896055817 23803943795765213922041863)
        ·
          refine ⟨35705915693647820883062795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23803943795765213922041863 35705915693647820883062795)
          ·
            refine ⟨53558873540471731324594193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35705915693647820883062795 53558873540471731324594193)
            ·
              refine ⟨40169155155353798493445645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53558873540471731324594193 40169155155353798493445645)
              ·
                refine ⟨15063433183257674435042117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40169155155353798493445645 15063433183257674435042117)
                ·
                  refine ⟨2824393721860813956570397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15063433183257674435042117 2824393721860813956570397)
                  ·
                    refine ⟨1059147645697805233713899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824393721860813956570397 1059147645697805233713899)
                    ·
                      rfl

theorem cell22_3094024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_3094024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094024 prefixEnd_3094024 := by exact prefixLift 3094024
  have htrace : WordTrace (prefixWord ++ tailWord_3094024) baseStart_3094024 baseEnd_3094024 := by
    simpa [prefixWord, tailWord_3094024, baseEnd_3094024] using wordTrace_append hprefix tailTrace_3094024
  have hstable : (prefixWord ++ tailWord_3094024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094024).length < 2 ^ (prefixWord ++ tailWord_3094024).sum := by decide
  have hdescent : baseEnd_3094024 < baseStart_3094024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094026 : List Nat := [3, 1, 2, 2, 2, 3, 1, 4, 4]
def baseStart_3094026 : Nat := 118140960795 + 3094026 * 2 ^ 59
def prefixEnd_3094026 : Nat := 4983230072969 + 3 ^ 40 * 3094026 * 2
def baseEnd_3094026 : Nat := 353049443446225965054631

theorem tailTrace_3094026 : CollatzResearch.WordTrace tailWord_3094026 prefixEnd_3094026 353049443446225965054631 := by
  unfold tailWord_3094026
  simp only [CollatzResearch.WordTrace]
  refine ⟨28212099772219923604109483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75232266059253129610958621 28212099772219923604109483)
  ·
    refine ⟨42318149658329885406164225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28212099772219923604109483 42318149658329885406164225)
    ·
      refine ⟨31738612243747414054623169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42318149658329885406164225 31738612243747414054623169)
      ·
        refine ⟨23803959182810560540967377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31738612243747414054623169 23803959182810560540967377)
        ·
          refine ⟨17852969387107920405725533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23803959182810560540967377 17852969387107920405725533)
          ·
            refine ⟨6694863520165470152147075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17852969387107920405725533 6694863520165470152147075)
            ·
              refine ⟨10042295280248205228220613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694863520165470152147075 10042295280248205228220613)
              ·
                refine ⟨1882930365046538480291365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10042295280248205228220613 1882930365046538480291365)
                ·
                  refine ⟨353049443446225965054631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1882930365046538480291365 353049443446225965054631)
                  ·
                    rfl

theorem cell22_3094026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_3094026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094026 prefixEnd_3094026 := by exact prefixLift 3094026
  have htrace : WordTrace (prefixWord ++ tailWord_3094026) baseStart_3094026 baseEnd_3094026 := by
    simpa [prefixWord, tailWord_3094026, baseEnd_3094026] using wordTrace_append hprefix tailTrace_3094026
  have hstable : (prefixWord ++ tailWord_3094026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094026).length < 2 ^ (prefixWord ++ tailWord_3094026).sum := by decide
  have hdescent : baseEnd_3094026 < baseStart_3094026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094056 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3094056 : Nat := 118140960795 + 3094056 * 2 ^ 59
def prefixEnd_3094056 : Nat := 4983230072969 + 3 ^ 40 * 3094056 * 2
def baseEnd_3094056 : Nat := 1059158599951767816913801

theorem tailTrace_3094056 : CollatzResearch.WordTrace tailWord_3094056 prefixEnd_3094056 1059158599951767816913801 := by
  unfold tailWord_3094056
  simp only [CollatzResearch.WordTrace]
  refine ⟨56424746639385504770015011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75232995519180673026686681 56424746639385504770015011)
  ·
    refine ⟨84637119959078257155022517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56424746639385504770015011 84637119959078257155022517)
    ·
      refine ⟨7934729996163586608283361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84637119959078257155022517 7934729996163586608283361)
      ·
        refine ⟨5951047497122689956212521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7934729996163586608283361 5951047497122689956212521)
        ·
          refine ⟨4463285622842017467159391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5951047497122689956212521 4463285622842017467159391)
          ·
            refine ⟨6694928434263026200739087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463285622842017467159391 6694928434263026200739087)
            ·
              refine ⟨10042392651394539301108631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6694928434263026200739087 10042392651394539301108631)
              ·
                refine ⟨15063588977091808951662947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10042392651394539301108631 15063588977091808951662947)
                ·
                  refine ⟨22595383465637713427494421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15063588977091808951662947 22595383465637713427494421)
                  ·
                    refine ⟨1059158599951767816913801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22595383465637713427494421 1059158599951767816913801)
                    ·
                      rfl

theorem cell22_3094056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3094056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094056 prefixEnd_3094056 := by exact prefixLift 3094056
  have htrace : WordTrace (prefixWord ++ tailWord_3094056) baseStart_3094056 baseEnd_3094056 := by
    simpa [prefixWord, tailWord_3094056, baseEnd_3094056] using wordTrace_append hprefix tailTrace_3094056
  have hstable : (prefixWord ++ tailWord_3094056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094056).length < 2 ^ (prefixWord ++ tailWord_3094056).sum := by decide
  have hdescent : baseEnd_3094056 < baseStart_3094056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094120 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 1, 3]
def baseStart_3094120 : Nat := 118140960795 + 3094120 * 2 ^ 59
def prefixEnd_3094120 : Nat := 4983230072969 + 3 ^ 40 * 3094120 * 2
def baseEnd_3094120 : Nat := 1059180508459692983313605

theorem tailTrace_3094120 : CollatzResearch.WordTrace tailWord_3094120 prefixEnd_3094120 1059180508459692983313605 := by
  unfold tailWord_3094120
  simp only [CollatzResearch.WordTrace]
  refine ⟨56425913775269574235179907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75234551700359432313573209 56425913775269574235179907)
  ·
    refine ⟨84638870662904361352769861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56425913775269574235179907 84638870662904361352769861)
    ·
      refine ⟨15869788249294567753644349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84638870662904361352769861 15869788249294567753644349)
      ·
        refine ⟨5951170593485462907616631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15869788249294567753644349 5951170593485462907616631)
        ·
          refine ⟨8926755890228194361424947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5951170593485462907616631 8926755890228194361424947)
          ·
            refine ⟨13390133835342291542137421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8926755890228194361424947 13390133835342291542137421)
            ·
              refine ⟨5021300188253359328301533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13390133835342291542137421 5021300188253359328301533)
              ·
                refine ⟨1882987570595009748113075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5021300188253359328301533 1882987570595009748113075)
                ·
                  refine ⟨2824481355892514622169613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1882987570595009748113075 2824481355892514622169613)
                  ·
                    refine ⟨1059180508459692983313605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824481355892514622169613 1059180508459692983313605)
                    ·
                      rfl

theorem cell22_3094120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_3094120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094120 prefixEnd_3094120 := by exact prefixLift 3094120
  have htrace : WordTrace (prefixWord ++ tailWord_3094120) baseStart_3094120 baseEnd_3094120 := by
    simpa [prefixWord, tailWord_3094120, baseEnd_3094120] using wordTrace_append hprefix tailTrace_3094120
  have hstable : (prefixWord ++ tailWord_3094120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094120).length < 2 ^ (prefixWord ++ tailWord_3094120).sum := by decide
  have hdescent : baseEnd_3094120 < baseStart_3094120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094176 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_3094176 : Nat := 118140960795 + 3094176 * 2 ^ 59
def prefixEnd_3094176 : Nat := 4983230072969 + 3 ^ 40 * 3094176 * 2
def baseEnd_3094176 : Nat := 1059199678404127503913433

theorem tailTrace_3094176 : CollatzResearch.WordTrace tailWord_3094176 prefixEnd_3094176 1059199678404127503913433 := by
  unfold tailWord_3094176
  simp only [CollatzResearch.WordTrace]
  refine ⟨56426935019168135017199191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75235913358890846689598921 56426935019168135017199191)
  ·
    refine ⟨84640402528752202525798787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56426935019168135017199191 84640402528752202525798787)
    ·
      refine ⟨126960603793128303788698181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84640402528752202525798787 126960603793128303788698181)
      ·
        refine ⟨23805113211211556960380909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126960603793128303788698181 23805113211211556960380909)
        ·
          refine ⟨8926917454204333860142841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23805113211211556960380909 8926917454204333860142841)
          ·
            refine ⟨6695188090653250395107131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8926917454204333860142841 6695188090653250395107131)
            ·
              refine ⟨10042782135979875592660697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6695188090653250395107131 10042782135979875592660697)
              ·
                refine ⟨7532086601984906694495523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10042782135979875592660697 7532086601984906694495523)
                ·
                  refine ⟨11298129902977360041743285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7532086601984906694495523 11298129902977360041743285)
                  ·
                    refine ⟨1059199678404127503913433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11298129902977360041743285 1059199678404127503913433)
                    ·
                      rfl

theorem cell22_3094176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_3094176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094176 prefixEnd_3094176 := by exact prefixLift 3094176
  have htrace : WordTrace (prefixWord ++ tailWord_3094176) baseStart_3094176 baseEnd_3094176 := by
    simpa [prefixWord, tailWord_3094176, baseEnd_3094176] using wordTrace_append hprefix tailTrace_3094176
  have hstable : (prefixWord ++ tailWord_3094176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094176).length < 2 ^ (prefixWord ++ tailWord_3094176).sum := by decide
  have hdescent : baseEnd_3094176 < baseStart_3094176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094206 : List Nat := [4, 2, 1, 1, 2, 2, 3, 7]
def baseStart_3094206 : Nat := 118140960795 + 3094206 * 2 ^ 59
def prefixEnd_3094206 : Nat := 4983230072969 + 3 ^ 40 * 3094206 * 2
def baseEnd_3094206 : Nat := 117689994224135269518149

theorem tailTrace_3094206 : CollatzResearch.WordTrace tailWord_3094206 prefixEnd_3094206 117689994224135269518149 := by
  unfold tailWord_3094206
  simp only [CollatzResearch.WordTrace]
  refine ⟨14106870528528448144748809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75236642818818390105326981 14106870528528448144748809)
  ·
    refine ⟨10580152896396336108561607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14106870528528448144748809 10580152896396336108561607)
    ·
      refine ⟨15870229344594504162842411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10580152896396336108561607 15870229344594504162842411)
      ·
        refine ⟨23805344016891756244263617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15870229344594504162842411 23805344016891756244263617)
        ·
          refine ⟨17854008012668817183197713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23805344016891756244263617 17854008012668817183197713)
          ·
            refine ⟨13390506009501612887398285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17854008012668817183197713 13390506009501612887398285)
            ·
              refine ⟨5021439753563104832774357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13390506009501612887398285 5021439753563104832774357)
              ·
                refine ⟨117689994224135269518149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5021439753563104832774357 117689994224135269518149)
                ·
                  rfl

theorem cell22_3094206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_3094206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094206 prefixEnd_3094206 := by exact prefixLift 3094206
  have htrace : WordTrace (prefixWord ++ tailWord_3094206) baseStart_3094206 baseEnd_3094206 := by
    simpa [prefixWord, tailWord_3094206, baseEnd_3094206] using wordTrace_append hprefix tailTrace_3094206
  have hstable : (prefixWord ++ tailWord_3094206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094206).length < 2 ^ (prefixWord ++ tailWord_3094206).sum := by decide
  have hdescent : baseEnd_3094206 < baseStart_3094206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094251 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 5]
def baseStart_3094251 : Nat := 118140960795 + 3094251 * 2 ^ 59
def prefixEnd_3094251 : Nat := 4983230072969 + 3 ^ 40 * 3094251 * 2
def baseEnd_3094251 : Nat := 353075117478950769429401

theorem tailTrace_3094251 : CollatzResearch.WordTrace tailWord_3094251 prefixEnd_3094251 353075117478950769429401 := by
  unfold tailWord_3094251
  simp only [CollatzResearch.WordTrace]
  refine ⟨112856605513064557843378607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75237737008709705228919071 112856605513064557843378607)
  ·
    refine ⟨169284908269596836765067911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112856605513064557843378607 169284908269596836765067911)
    ·
      refine ⟨253927362404395255147601867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169284908269596836765067911 253927362404395255147601867)
      ·
        refine ⟨380891043606592882721402801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253927362404395255147601867 380891043606592882721402801)
        ·
          refine ⟨285668282704944662041052101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 380891043606592882721402801 285668282704944662041052101)
          ·
            refine ⟨53562803007177124132697269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 285668282704944662041052101 53562803007177124132697269)
            ·
              refine ⟨5021512781922855387440369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53562803007177124132697269 5021512781922855387440369)
              ·
                refine ⟨3766134586442141540580277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021512781922855387440369 3766134586442141540580277)
                ·
                  refine ⟨353075117478950769429401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766134586442141540580277 353075117478950769429401)
                  ·
                    rfl

theorem cell22_3094251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 5].length) (baseStart_3094251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094251 prefixEnd_3094251 := by exact prefixLift 3094251
  have htrace : WordTrace (prefixWord ++ tailWord_3094251) baseStart_3094251 baseEnd_3094251 := by
    simpa [prefixWord, tailWord_3094251, baseEnd_3094251] using wordTrace_append hprefix tailTrace_3094251
  have hstable : (prefixWord ++ tailWord_3094251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094251).length < 2 ^ (prefixWord ++ tailWord_3094251).sum := by decide
  have hdescent : baseEnd_3094251 < baseStart_3094251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094264 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_3094264 : Nat := 118140960795 + 3094264 * 2 ^ 59
def prefixEnd_3094264 : Nat := 4983230072969 + 3 ^ 40 * 3094264 * 2
def baseEnd_3094264 : Nat := 1059229802602524607713163

theorem tailTrace_3094264 : CollatzResearch.WordTrace tailWord_3094264 prefixEnd_3094264 1059229802602524607713163 := by
  unfold tailWord_3094264
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428539831008730531800923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75238053108011640709067897 56428539831008730531800923)
  ·
    refine ⟨84642809746513095797701385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56428539831008730531800923 84642809746513095797701385)
    ·
      refine ⟨63482107309884821848276039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84642809746513095797701385 63482107309884821848276039)
      ·
        refine ⟨95223160964827232772414059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63482107309884821848276039 95223160964827232772414059)
        ·
          refine ⟨142834741447240849158621089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95223160964827232772414059 142834741447240849158621089)
          ·
            refine ⟨107126056085430636868965817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142834741447240849158621089 107126056085430636868965817)
            ·
              refine ⟨80344542064072977651724363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107126056085430636868965817 80344542064072977651724363)
              ·
                refine ⟨120516813096109466477586545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80344542064072977651724363 120516813096109466477586545)
                ·
                  refine ⟨90387609822082099858189909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120516813096109466477586545 90387609822082099858189909)
                  ·
                    refine ⟨1059229802602524607713163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90387609822082099858189909 1059229802602524607713163)
                    ·
                      rfl

theorem cell22_3094264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_3094264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094264 prefixEnd_3094264 := by exact prefixLift 3094264
  have htrace : WordTrace (prefixWord ++ tailWord_3094264) baseStart_3094264 baseEnd_3094264 := by
    simpa [prefixWord, tailWord_3094264, baseEnd_3094264] using wordTrace_append hprefix tailTrace_3094264
  have hstable : (prefixWord ++ tailWord_3094264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094264).length < 2 ^ (prefixWord ++ tailWord_3094264).sum := by decide
  have hdescent : baseEnd_3094264 < baseStart_3094264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094268 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 5]
def baseStart_3094268 : Nat := 118140960795 + 3094268 * 2 ^ 59
def prefixEnd_3094268 : Nat := 4983230072969 + 3 ^ 40 * 3094268 * 2
def baseEnd_3094268 : Nat := 353077057294756643537717

theorem tailTrace_3094268 : CollatzResearch.WordTrace tailWord_3094268 prefixEnd_3094268 353077057294756643537717 := by
  unfold tailWord_3094268
  simp only [CollatzResearch.WordTrace]
  refine ⟨56428612777001484873373729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75238150369335313164498305 56428612777001484873373729)
  ·
    refine ⟨42321459582751113655030297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56428612777001484873373729 42321459582751113655030297)
    ·
      refine ⟨31741094687063335241272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42321459582751113655030297 31741094687063335241272723)
      ·
        refine ⟨47611642030595002861909085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31741094687063335241272723 47611642030595002861909085)
        ·
          refine ⟨17854365761473126073215907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47611642030595002861909085 17854365761473126073215907)
          ·
            refine ⟨26781548642209689109823861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17854365761473126073215907 26781548642209689109823861)
            ·
              refine ⟨2510770185207158354045987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26781548642209689109823861 2510770185207158354045987)
              ·
                refine ⟨3766155277810737531068981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510770185207158354045987 3766155277810737531068981)
                ·
                  refine ⟨353077057294756643537717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766155277810737531068981 353077057294756643537717)
                  ·
                    rfl

theorem cell22_3094268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_3094268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094268 prefixEnd_3094268 := by exact prefixLift 3094268
  have htrace : WordTrace (prefixWord ++ tailWord_3094268) baseStart_3094268 baseEnd_3094268 := by
    simpa [prefixWord, tailWord_3094268, baseEnd_3094268] using wordTrace_append hprefix tailTrace_3094268
  have hstable : (prefixWord ++ tailWord_3094268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094268).length < 2 ^ (prefixWord ++ tailWord_3094268).sum := by decide
  have hdescent : baseEnd_3094268 < baseStart_3094268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094298 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_3094298 : Nat := 118140960795 + 3094298 * 2 ^ 59
def prefixEnd_3094298 : Nat := 4983230072969 + 3 ^ 40 * 3094298 * 2
def baseEnd_3094298 : Nat := 1059241441497359852363059

theorem tailTrace_3094298 : CollatzResearch.WordTrace tailWord_3094298 prefixEnd_3094298 1059241441497359852363059 := by
  unfold tailWord_3094298
  simp only [CollatzResearch.WordTrace]
  refine ⟨28214579935973571217584887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75238879829262856580226365 28214579935973571217584887)
  ·
    refine ⟨42321869903960356826377331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28214579935973571217584887 42321869903960356826377331)
    ·
      refine ⟨63482804855940535239565997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42321869903960356826377331 63482804855940535239565997)
      ·
        refine ⟨23806051820977700714837249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63482804855940535239565997 23806051820977700714837249)
        ·
          refine ⟨17854538865733275536127937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23806051820977700714837249 17854538865733275536127937)
          ·
            refine ⟨13390904149299956652095953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17854538865733275536127937 13390904149299956652095953)
            ·
              refine ⟨10043178111974967489071965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13390904149299956652095953 10043178111974967489071965)
              ·
                refine ⟨3766191791990612808401987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10043178111974967489071965 3766191791990612808401987)
                ·
                  refine ⟨5649287687985919212602981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3766191791990612808401987 5649287687985919212602981)
                  ·
                    refine ⟨1059241441497359852363059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5649287687985919212602981 1059241441497359852363059)
                    ·
                      rfl

theorem cell22_3094298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_3094298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094298 prefixEnd_3094298 := by exact prefixLift 3094298
  have htrace : WordTrace (prefixWord ++ tailWord_3094298) baseStart_3094298 baseEnd_3094298 := by
    simpa [prefixWord, tailWord_3094298, baseEnd_3094298] using wordTrace_append hprefix tailTrace_3094298
  have hstable : (prefixWord ++ tailWord_3094298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094298).length < 2 ^ (prefixWord ++ tailWord_3094298).sum := by decide
  have hdescent : baseEnd_3094298 < baseStart_3094298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094364 : List Nat := [2, 2, 4, 2, 2, 2, 2, 2, 4]
def baseStart_3094364 : Nat := 118140960795 + 3094364 * 2 ^ 59
def prefixEnd_3094364 : Nat := 4983230072969 + 3 ^ 40 * 3094364 * 2
def baseEnd_3094364 : Nat := 353088011548719226737619

theorem tailTrace_3094364 : CollatzResearch.WordTrace tailWord_3094364 prefixEnd_3094364 353088011548719226737619 := by
  unfold tailWord_3094364
  simp only [CollatzResearch.WordTrace]
  refine ⟨56430363480827589071121073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75240484641103452094828097 56430363480827589071121073)
  ·
    refine ⟨42322772610620691803340805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56430363480827589071121073 42322772610620691803340805)
    ·
      refine ⟨7935519864491379713126401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42322772610620691803340805 7935519864491379713126401)
      ·
        refine ⟨5951639898368534784844801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7935519864491379713126401 5951639898368534784844801)
        ·
          refine ⟨4463729923776401088633601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5951639898368534784844801 4463729923776401088633601)
          ·
            refine ⟨3347797442832300816475201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463729923776401088633601 3347797442832300816475201)
            ·
              refine ⟨2510848082124225612356401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347797442832300816475201 2510848082124225612356401)
              ·
                refine ⟨1883136061593169209267301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510848082124225612356401 1883136061593169209267301)
                ·
                  refine ⟨353088011548719226737619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883136061593169209267301 353088011548719226737619)
                  ·
                    rfl

theorem cell22_3094364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_3094364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094364 prefixEnd_3094364 := by exact prefixLift 3094364
  have htrace : WordTrace (prefixWord ++ tailWord_3094364) baseStart_3094364 baseEnd_3094364 := by
    simpa [prefixWord, tailWord_3094364, baseEnd_3094364] using wordTrace_append hprefix tailTrace_3094364
  have hstable : (prefixWord ++ tailWord_3094364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094364).length < 2 ^ (prefixWord ++ tailWord_3094364).sum := by decide
  have hdescent : baseEnd_3094364 < baseStart_3094364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094373 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_3094373 : Nat := 118140960795 + 3094373 * 2 ^ 59
def prefixEnd_3094373 : Nat := 4983230072969 + 3 ^ 40 * 3094373 * 2
def baseEnd_3094373 : Nat := 1059267115530084656737829

theorem tailTrace_3094373 : CollatzResearch.WordTrace tailWord_3094373 prefixEnd_3094373 1059267115530084656737829 := by
  unfold tailWord_3094373
  simp only [CollatzResearch.WordTrace]
  refine ⟨112861055218622572679319773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75240703479081715119546515 112861055218622572679319773)
  ·
    refine ⟨42322895706983464754744915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112861055218622572679319773 42322895706983464754744915)
    ·
      refine ⟨63484343560475197132117373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42322895706983464754744915 63484343560475197132117373)
      ·
        refine ⟨23806628835178198924544015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63484343560475197132117373 23806628835178198924544015)
        ·
          refine ⟨35709943252767298386816023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23806628835178198924544015 35709943252767298386816023)
          ·
            refine ⟨53564914879150947580224035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35709943252767298386816023 53564914879150947580224035)
            ·
              refine ⟨80347372318726421370336053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53564914879150947580224035 80347372318726421370336053)
              ·
                refine ⟨7532566154880602003469005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80347372318726421370336053 7532566154880602003469005)
                ·
                  refine ⟨2824712308080225751300877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7532566154880602003469005 2824712308080225751300877)
                  ·
                    refine ⟨1059267115530084656737829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824712308080225751300877 1059267115530084656737829)
                    ·
                      rfl

theorem cell22_3094373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_3094373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094373 prefixEnd_3094373 := by exact prefixLift 3094373
  have htrace : WordTrace (prefixWord ++ tailWord_3094373) baseStart_3094373 baseEnd_3094373 := by
    simpa [prefixWord, tailWord_3094373, baseEnd_3094373] using wordTrace_append hprefix tailTrace_3094373
  have hstable : (prefixWord ++ tailWord_3094373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094373).length < 2 ^ (prefixWord ++ tailWord_3094373).sum := by decide
  have hdescent : baseEnd_3094373 < baseStart_3094373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094386 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 9]
def baseStart_3094386 : Nat := 118140960795 + 3094386 * 2 ^ 59
def prefixEnd_3094386 : Nat := 4983230072969 + 3 ^ 40 * 3094386 * 2
def baseEnd_3094386 : Nat := 353090521898585652054263

theorem tailTrace_3094386 : CollatzResearch.WordTrace tailWord_3094386 prefixEnd_3094386 353090521898585652054263 := by
  unfold tailWord_3094386
  simp only [CollatzResearch.WordTrace]
  refine ⟨28215382341893868974885753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75241019578383650599695341 28215382341893868974885753)
  ·
    refine ⟨21161536756420401731164315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28215382341893868974885753 21161536756420401731164315)
    ·
      refine ⟨31742305134630602596746473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21161536756420401731164315 31742305134630602596746473)
      ·
        refine ⟨23806728850972951947559855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31742305134630602596746473 23806728850972951947559855)
        ·
          refine ⟨35710093276459427921339783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23806728850972951947559855 35710093276459427921339783)
          ·
            refine ⟨53565139914689141882009675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35710093276459427921339783 53565139914689141882009675)
            ·
              refine ⟨80347709872033712823014513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53565139914689141882009675 80347709872033712823014513)
              ·
                refine ⟨60260782404025284617260885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80347709872033712823014513 60260782404025284617260885)
                ·
                  refine ⟨353090521898585652054263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 60260782404025284617260885 353090521898585652054263)
                  ·
                    rfl

theorem cell22_3094386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_3094386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094386 prefixEnd_3094386 := by exact prefixLift 3094386
  have htrace : WordTrace (prefixWord ++ tailWord_3094386) baseStart_3094386 baseEnd_3094386 := by
    simpa [prefixWord, tailWord_3094386, baseEnd_3094386] using wordTrace_append hprefix tailTrace_3094386
  have hstable : (prefixWord ++ tailWord_3094386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094386).length < 2 ^ (prefixWord ++ tailWord_3094386).sum := by decide
  have hdescent : baseEnd_3094386 < baseStart_3094386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094420 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3094420 : Nat := 118140960795 + 3094420 * 2 ^ 59
def prefixEnd_3094420 : Nat := 4983230072969 + 3 ^ 40 * 3094420 * 2
def baseEnd_3094420 : Nat := 353094401530197400270895

theorem tailTrace_3094420 : CollatzResearch.WordTrace tailWord_3094420 prefixEnd_3094420 353094401530197400270895 := by
  unfold tailWord_3094420
  simp only [CollatzResearch.WordTrace]
  refine ⟨56431384724726149853140357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75241846299634866470853809 56431384724726149853140357)
  ·
    refine ⟨10580884635886153097463817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56431384724726149853140357 10580884635886153097463817)
    ·
      refine ⟨7935663476914614823097863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10580884635886153097463817 7935663476914614823097863)
      ·
        refine ⟨11903495215371922234646795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7935663476914614823097863 11903495215371922234646795)
        ·
          refine ⟨17855242823057883351970193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11903495215371922234646795 17855242823057883351970193)
          ·
            refine ⟨13391432117293412513977645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17855242823057883351970193 13391432117293412513977645)
            ·
              refine ⟨5021787043985029692741617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13391432117293412513977645 5021787043985029692741617)
              ·
                refine ⟨3766340282988772269556213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5021787043985029692741617 3766340282988772269556213)
                ·
                  refine ⟨353094401530197400270895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3766340282988772269556213 353094401530197400270895)
                  ·
                    rfl

theorem cell22_3094420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3094420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094420 prefixEnd_3094420 := by exact prefixLift 3094420
  have htrace : WordTrace (prefixWord ++ tailWord_3094420) baseStart_3094420 baseEnd_3094420 := by
    simpa [prefixWord, tailWord_3094420, baseEnd_3094420] using wordTrace_append hprefix tailTrace_3094420
  have hstable : (prefixWord ++ tailWord_3094420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094420).length < 2 ^ (prefixWord ++ tailWord_3094420).sum := by decide
  have hdescent : baseEnd_3094420 < baseStart_3094420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094463 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 6, 3]
def baseStart_3094463 : Nat := 118140960795 + 3094463 * 2 ^ 59
def prefixEnd_3094463 : Nat := 4983230072969 + 3 ^ 40 * 3094463 * 2
def baseEnd_3094463 : Nat := 1059297924369354421987553

theorem tailTrace_3094463 : CollatzResearch.WordTrace tailWord_3094463 prefixEnd_3094463 1059297924369354421987553 := by
  unfold tailWord_3094463
  simp only [CollatzResearch.WordTrace]
  refine ⟨112864337788296518050096043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75242891858864345366730695 112864337788296518050096043)
  ·
    refine ⟨169296506682444777075144065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112864337788296518050096043 169296506682444777075144065)
    ·
      refine ⟨126972380011833582806358049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169296506682444777075144065 126972380011833582806358049)
      ·
        refine ⟨95229285008875187104768537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126972380011833582806358049 95229285008875187104768537)
        ·
          refine ⟨71421963756656390328576403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95229285008875187104768537 71421963756656390328576403)
          ·
            refine ⟨107132945634984585492864605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71421963756656390328576403 107132945634984585492864605)
            ·
              refine ⟨40174854613119219559824227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107132945634984585492864605 40174854613119219559824227)
              ·
                refine ⟨60262281919678829339736341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40174854613119219559824227 60262281919678829339736341)
                ·
                  refine ⟨2824794464984945125300141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60262281919678829339736341 2824794464984945125300141)
                  ·
                    refine ⟨1059297924369354421987553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824794464984945125300141 1059297924369354421987553)
                    ·
                      rfl

theorem cell22_3094463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_3094463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094463 prefixEnd_3094463 := by exact prefixLift 3094463
  have htrace : WordTrace (prefixWord ++ tailWord_3094463) baseStart_3094463 baseEnd_3094463 := by
    simpa [prefixWord, tailWord_3094463, baseEnd_3094463] using wordTrace_append hprefix tailTrace_3094463
  have hstable : (prefixWord ++ tailWord_3094463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094463).length < 2 ^ (prefixWord ++ tailWord_3094463).sum := by decide
  have hdescent : baseEnd_3094463 < baseStart_3094463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094482 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_3094482 : Nat := 118140960795 + 3094482 * 2 ^ 59
def prefixEnd_3094482 : Nat := 4983230072969 + 3 ^ 40 * 3094482 * 2
def baseEnd_3094482 : Nat := 353101476152548235254165

theorem tailTrace_3094482 : CollatzResearch.WordTrace tailWord_3094482 prefixEnd_3094482 353101476152548235254165 := by
  unfold tailWord_3094482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28216257693806921073759425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75243353850151789530025133 28216257693806921073759425)
  ·
    refine ⟨21162193270355190805319569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28216257693806921073759425 21162193270355190805319569)
    ·
      refine ⟨15871644952766393103989677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21162193270355190805319569 15871644952766393103989677)
      ·
        refine ⟨5951866857287397413996129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15871644952766393103989677 5951866857287397413996129)
        ·
          refine ⟨4463900142965548060497097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5951866857287397413996129 4463900142965548060497097)
          ·
            refine ⟨3347925107224161045372823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4463900142965548060497097 3347925107224161045372823)
            ·
              refine ⟨5021887660836241568059235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3347925107224161045372823 5021887660836241568059235)
              ·
                refine ⟨7532831491254362352088853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021887660836241568059235 7532831491254362352088853)
                ·
                  refine ⟨353101476152548235254165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7532831491254362352088853 353101476152548235254165)
                  ·
                    rfl

theorem cell22_3094482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_3094482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094482 prefixEnd_3094482 := by exact prefixLift 3094482
  have htrace : WordTrace (prefixWord ++ tailWord_3094482) baseStart_3094482 baseEnd_3094482 := by
    simpa [prefixWord, tailWord_3094482, baseEnd_3094482] using wordTrace_append hprefix tailTrace_3094482
  have hstable : (prefixWord ++ tailWord_3094482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094482).length < 2 ^ (prefixWord ++ tailWord_3094482).sum := by decide
  have hdescent : baseEnd_3094482 < baseStart_3094482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094497 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 2, 3]
def baseStart_3094497 : Nat := 118140960795 + 3094497 * 2 ^ 59
def prefixEnd_3094497 : Nat := 4983230072969 + 3 ^ 40 * 3094497 * 2
def baseEnd_3094497 : Nat := 1059309563264189666637449

theorem tailTrace_3094497 : CollatzResearch.WordTrace tailWord_3094497 prefixEnd_3094497 1059309563264189666637449 := by
  unfold tailWord_3094497
  simp only [CollatzResearch.WordTrace]
  refine ⟨112865577870173341856833745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75243718580115561237889163 112865577870173341856833745)
  ·
    refine ⟨84649183402630006392625309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112865577870173341856833745 84649183402630006392625309)
    ·
      refine ⟨31743443775986252397234491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84649183402630006392625309 31743443775986252397234491)
      ·
        refine ⟨47615165663979378595851737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31743443775986252397234491 47615165663979378595851737)
        ·
          refine ⟨35711374247984533946888803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47615165663979378595851737 35711374247984533946888803)
          ·
            refine ⟨53567061371976800920333205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35711374247984533946888803 53567061371976800920333205)
            ·
              refine ⟨2510956001811412543140619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 53567061371976800920333205 2510956001811412543140619)
              ·
                refine ⟨3766434002717118814710929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2510956001811412543140619 3766434002717118814710929)
                ·
                  refine ⟨2824825502037839111033197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3766434002717118814710929 2824825502037839111033197)
                  ·
                    refine ⟨1059309563264189666637449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824825502037839111033197 1059309563264189666637449)
                    ·
                      rfl

theorem cell22_3094497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_3094497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094497 prefixEnd_3094497 := by exact prefixLift 3094497
  have htrace : WordTrace (prefixWord ++ tailWord_3094497) baseStart_3094497 baseEnd_3094497 := by
    simpa [prefixWord, tailWord_3094497, baseEnd_3094497] using wordTrace_append hprefix tailTrace_3094497
  have hstable : (prefixWord ++ tailWord_3094497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094497).length < 2 ^ (prefixWord ++ tailWord_3094497).sum := by decide
  have hdescent : baseEnd_3094497 < baseStart_3094497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094615 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3094615 : Nat := 118140960795 + 3094615 * 2 ^ 59
def prefixEnd_3094615 : Nat := 4983230072969 + 3 ^ 40 * 3094615 * 2
def baseEnd_3094615 : Nat := 1059349957075676692187087

theorem tailTrace_3094615 : CollatzResearch.WordTrace tailWord_3094615 prefixEnd_3094615 1059349957075676692187087 := by
  unfold tailWord_3094615
  simp only [CollatzResearch.WordTrace]
  refine ⟨112869881683745848009629299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75246587789163898673086199 112869881683745848009629299)
  ·
    refine ⟨169304822525618772014443949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112869881683745848009629299 169304822525618772014443949)
    ·
      refine ⟨63489308447107039505416481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169304822525618772014443949 63489308447107039505416481)
      ·
        refine ⟨47616981335330279629062361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63489308447107039505416481 47616981335330279629062361)
        ·
          refine ⟨35712736001497709721796771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47616981335330279629062361 35712736001497709721796771)
          ·
            refine ⟨53569104002246564582695157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35712736001497709721796771 53569104002246564582695157)
            ·
              refine ⟨5022103500210615429627671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53569104002246564582695157 5022103500210615429627671)
              ·
                refine ⟨7533155250315923144441507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5022103500210615429627671 7533155250315923144441507)
                ·
                  refine ⟨11299732875473884716662261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7533155250315923144441507 11299732875473884716662261)
                  ·
                    refine ⟨1059349957075676692187087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11299732875473884716662261 1059349957075676692187087)
                    ·
                      rfl

theorem cell22_3094615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3094615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094615 prefixEnd_3094615 := by exact prefixLift 3094615
  have htrace : WordTrace (prefixWord ++ tailWord_3094615) baseStart_3094615 baseEnd_3094615 := by
    simpa [prefixWord, tailWord_3094615, baseEnd_3094615] using wordTrace_append hprefix tailTrace_3094615
  have hstable : (prefixWord ++ tailWord_3094615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094615).length < 2 ^ (prefixWord ++ tailWord_3094615).sum := by decide
  have hdescent : baseEnd_3094615 < baseStart_3094615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094666 : List Nat := [3, 1, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_3094666 : Nat := 118140960795 + 3094666 * 2 ^ 59
def prefixEnd_3094666 : Nat := 4983230072969 + 3 ^ 40 * 3094666 * 2
def baseEnd_3094666 : Nat := 1059367415417929559161931

theorem tailTrace_3094666 : CollatzResearch.WordTrace tailWord_3094666 prefixEnd_3094666 1059367415417929559161931 := by
  unfold tailWord_3094666
  simp only [CollatzResearch.WordTrace]
  refine ⟨28217935451640270929933963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75247827871040722479823901 28217935451640270929933963)
  ·
    refine ⟨42326903177460406394900945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28217935451640270929933963 42326903177460406394900945)
    ·
      refine ⟨31745177383095304796175709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42326903177460406394900945 31745177383095304796175709)
      ·
        refine ⟨11904441518660739298565891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31745177383095304796175709 11904441518660739298565891)
        ·
          refine ⟨17856662277991108947848837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11904441518660739298565891 17856662277991108947848837)
          ·
            refine ⟨3348124177123332927721657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17856662277991108947848837 3348124177123332927721657)
            ·
              refine ⟨2511093132842499695791243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3348124177123332927721657 2511093132842499695791243)
              ·
                refine ⟨3766639699263749543686865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2511093132842499695791243 3766639699263749543686865)
                ·
                  refine ⟨2824979774447812157765149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3766639699263749543686865 2824979774447812157765149)
                  ·
                    refine ⟨1059367415417929559161931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2824979774447812157765149 1059367415417929559161931)
                    ·
                      rfl

theorem cell22_3094666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_3094666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094666 prefixEnd_3094666 := by exact prefixLift 3094666
  have htrace : WordTrace (prefixWord ++ tailWord_3094666) baseStart_3094666 baseEnd_3094666 := by
    simpa [prefixWord, tailWord_3094666, baseEnd_3094666] using wordTrace_append hprefix tailTrace_3094666
  have hstable : (prefixWord ++ tailWord_3094666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094666).length < 2 ^ (prefixWord ++ tailWord_3094666).sum := by decide
  have hdescent : baseEnd_3094666 < baseStart_3094666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094711 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 1, 3]
def baseStart_3094711 : Nat := 118140960795 + 3094711 * 2 ^ 59
def prefixEnd_3094711 : Nat := 4983230072969 + 3 ^ 40 * 3094711 * 2
def baseEnd_3094711 : Nat := 1059382819837564441786793

theorem tailTrace_3094711 : CollatzResearch.WordTrace tailWord_3094711 prefixEnd_3094711 1059382819837564441786793 := by
  unfold tailWord_3094711
  simp only [CollatzResearch.WordTrace]
  refine ⟨112873383091398056405123987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75248922060932037603415991 112873383091398056405123987)
  ·
    refine ⟨169310074637097084607685981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112873383091398056405123987 169310074637097084607685981)
    ·
      refine ⟨63491277988911406727882243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169310074637097084607685981 63491277988911406727882243)
      ·
        refine ⟨95236916983367110091823365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63491277988911406727882243 95236916983367110091823365)
        ·
          refine ⟨17856921934381333142216881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95236916983367110091823365 17856921934381333142216881)
          ·
            refine ⟨13392691450785999856662661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17856921934381333142216881 13392691450785999856662661)
            ·
              refine ⟨2511129647022374973124249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13392691450785999856662661 2511129647022374973124249)
              ·
                refine ⟨1883347235266781229843187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2511129647022374973124249 1883347235266781229843187)
                ·
                  refine ⟨2825020852900171844764781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883347235266781229843187 2825020852900171844764781)
                  ·
                    refine ⟨1059382819837564441786793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825020852900171844764781 1059382819837564441786793)
                    ·
                      rfl

theorem cell22_3094711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 3].length) (baseStart_3094711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094711 prefixEnd_3094711 := by exact prefixLift 3094711
  have htrace : WordTrace (prefixWord ++ tailWord_3094711) baseStart_3094711 baseEnd_3094711 := by
    simpa [prefixWord, tailWord_3094711, baseEnd_3094711] using wordTrace_append hprefix tailTrace_3094711
  have hstable : (prefixWord ++ tailWord_3094711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094711).length < 2 ^ (prefixWord ++ tailWord_3094711).sum := by decide
  have hdescent : baseEnd_3094711 < baseStart_3094711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094735 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 6]
def baseStart_3094735 : Nat := 118140960795 + 3094735 * 2 ^ 59
def prefixEnd_3094735 : Nat := 4983230072969 + 3 ^ 40 * 3094735 * 2
def baseEnd_3094735 : Nat := 353130345176012126395573

theorem tailTrace_3094735 : CollatzResearch.WordTrace tailWord_3094735 prefixEnd_3094735 353130345176012126395573 := by
  unfold tailWord_3094735
  simp only [CollatzResearch.WordTrace]
  refine ⟨112874258443311108503997659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75249505628874072335998439 112874258443311108503997659)
  ·
    refine ⟨169311387664966662755996489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112874258443311108503997659 169311387664966662755996489)
    ·
      refine ⟨126983540748724997066997367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169311387664966662755996489 126983540748724997066997367)
      ·
        refine ⟨190475311123087495600496051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126983540748724997066997367 190475311123087495600496051)
        ·
          refine ⟨285712966684631243400744077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190475311123087495600496051 285712966684631243400744077)
          ·
            refine ⟨107142362506736716275279029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 285712966684631243400744077 107142362506736716275279029)
            ·
              refine ⟨10044596485006567150807409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107142362506736716275279029 10044596485006567150807409)
              ·
                refine ⟨7533447363754925363105557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10044596485006567150807409 7533447363754925363105557)
                ·
                  refine ⟨353130345176012126395573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7533447363754925363105557 353130345176012126395573)
                  ·
                    rfl

theorem cell22_3094735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 6].length) (baseStart_3094735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094735 prefixEnd_3094735 := by exact prefixLift 3094735
  have htrace : WordTrace (prefixWord ++ tailWord_3094735) baseStart_3094735 baseEnd_3094735 := by
    simpa [prefixWord, tailWord_3094735, baseEnd_3094735] using wordTrace_append hprefix tailTrace_3094735
  have hstable : (prefixWord ++ tailWord_3094735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094735).length < 2 ^ (prefixWord ++ tailWord_3094735).sum := by decide
  have hdescent : baseEnd_3094735 < baseStart_3094735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094782 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 3, 6]
def baseStart_3094782 : Nat := 118140960795 + 3094782 * 2 ^ 59
def prefixEnd_3094782 : Nat := 4983230072969 + 3 ^ 40 * 3094782 * 2
def baseEnd_3094782 : Nat := 1059407124588543923261575

theorem tailTrace_3094782 : CollatzResearch.WordTrace tailWord_3094782 prefixEnd_3094782 1059407124588543923261575 := by
  unfold tailWord_3094782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109496584267604441369825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75250648449427223687305733 14109496584267604441369825)
  ·
    refine ⟨10582122438200703331027369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14109496584267604441369825 10582122438200703331027369)
    ·
      refine ⟨7936591828650527498270527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10582122438200703331027369 7936591828650527498270527)
      ·
        refine ⟨11904887742975791247405791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7936591828650527498270527 11904887742975791247405791)
        ·
          refine ⟨17857331614463686871108687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11904887742975791247405791 17857331614463686871108687)
          ·
            refine ⟨26785997421695530306663031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17857331614463686871108687 26785997421695530306663031)
            ·
              refine ⟨40178996132543295459994547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26785997421695530306663031 40178996132543295459994547)
              ·
                refine ⟨60268494198814943189991821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40178996132543295459994547 60268494198814943189991821)
                ·
                  refine ⟨22600685324555603696246933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60268494198814943189991821 22600685324555603696246933)
                  ·
                    refine ⟨1059407124588543923261575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22600685324555603696246933 1059407124588543923261575)
                    ·
                      rfl

theorem cell22_3094782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_3094782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094782 prefixEnd_3094782 := by exact prefixLift 3094782
  have htrace : WordTrace (prefixWord ++ tailWord_3094782) baseStart_3094782 baseEnd_3094782 := by
    simpa [prefixWord, tailWord_3094782, baseEnd_3094782] using wordTrace_append hprefix tailTrace_3094782
  have hstable : (prefixWord ++ tailWord_3094782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094782).length < 2 ^ (prefixWord ++ tailWord_3094782).sum := by decide
  have hdescent : baseEnd_3094782 < baseStart_3094782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094795 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 2, 7]
def baseStart_3094795 : Nat := 118140960795 + 3094795 * 2 ^ 59
def prefixEnd_3094795 : Nat := 4983230072969 + 3 ^ 40 * 3094795 * 2
def baseEnd_3094795 : Nat := 1059411574754216222686535

theorem tailTrace_3094795 : CollatzResearch.WordTrace tailWord_3094795 prefixEnd_3094795 1059411574754216222686535 := by
  unfold tailWord_3094795
  simp only [CollatzResearch.WordTrace]
  refine ⟨112876446823093738751181839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75250964548729159167454559 112876446823093738751181839)
  ·
    refine ⟨169314670234640608126772759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112876446823093738751181839 169314670234640608126772759)
    ·
      refine ⟨253972005351960912190159139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169314670234640608126772759 253972005351960912190159139)
      ·
        refine ⟨380958008027941368285238709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253972005351960912190159139 380958008027941368285238709)
        ·
          refine ⟨35714813252619503276741129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 380958008027941368285238709 35714813252619503276741129)
          ·
            refine ⟨26786109939464627457555847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35714813252619503276741129 26786109939464627457555847)
            ·
              refine ⟨40179164909196941186333771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26786109939464627457555847 40179164909196941186333771)
              ·
                refine ⟨60268747363795411779500657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40179164909196941186333771 60268747363795411779500657)
                ·
                  refine ⟨45201560522846558834625493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60268747363795411779500657 45201560522846558834625493)
                  ·
                    refine ⟨1059411574754216222686535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45201560522846558834625493 1059411574754216222686535)
                    ·
                      rfl

theorem cell22_3094795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_3094795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094795 prefixEnd_3094795 := by exact prefixLift 3094795
  have htrace : WordTrace (prefixWord ++ tailWord_3094795) baseStart_3094795 baseEnd_3094795 := by
    simpa [prefixWord, tailWord_3094795, baseEnd_3094795] using wordTrace_append hprefix tailTrace_3094795
  have hstable : (prefixWord ++ tailWord_3094795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094795).length < 2 ^ (prefixWord ++ tailWord_3094795).sum := by decide
  have hdescent : baseEnd_3094795 < baseStart_3094795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094814 : List Nat := [4, 3, 2, 1, 1, 1, 10]
def baseStart_3094814 : Nat := 118140960795 + 3094814 * 2 ^ 59
def prefixEnd_3094814 : Nat := 4983230072969 + 3 ^ 40 * 3094814 * 2
def baseEnd_3094814 : Nat := 39237706623796537276351

theorem tailTrace_3094814 : CollatzResearch.WordTrace tailWord_3094814 prefixEnd_3094814 39237706623796537276351 := by
  unfold tailWord_3094814
  simp only [CollatzResearch.WordTrace]
  refine ⟨14109642476253113124515437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 75251426540016603330748997 14109642476253113124515437)
  ·
    refine ⟨5291115928594917421693289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14109642476253113124515437 5291115928594917421693289)
    ·
      refine ⟨3968336946446188066269967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5291115928594917421693289 3968336946446188066269967)
      ·
        refine ⟨5952505419669282099404951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3968336946446188066269967 5952505419669282099404951)
        ·
          refine ⟨8928758129503923149107427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952505419669282099404951 8928758129503923149107427)
          ·
            refine ⟨13393137194255884723661141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8928758129503923149107427 13393137194255884723661141)
            ·
              refine ⟨39237706623796537276351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13393137194255884723661141 39237706623796537276351)
              ·
                rfl

theorem cell22_3094814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 10].length) (baseStart_3094814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094814 prefixEnd_3094814 := by exact prefixLift 3094814
  have htrace : WordTrace (prefixWord ++ tailWord_3094814) baseStart_3094814 baseEnd_3094814 := by
    simpa [prefixWord, tailWord_3094814, baseEnd_3094814] using wordTrace_append hprefix tailTrace_3094814
  have hstable : (prefixWord ++ tailWord_3094814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094814).length < 2 ^ (prefixWord ++ tailWord_3094814).sum := by decide
  have hdescent : baseEnd_3094814 < baseStart_3094814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094880 : List Nat := [2, 1, 1, 3, 5, 2, 2, 2, 1, 3]
def baseStart_3094880 : Nat := 118140960795 + 3094880 * 2 ^ 59
def prefixEnd_3094880 : Nat := 4983230072969 + 3 ^ 40 * 3094880 * 2
def baseEnd_3094880 : Nat := 1059440671991304334311275

theorem tailTrace_3094880 : CollatzResearch.WordTrace tailWord_3094880 prefixEnd_3094880 1059440671991304334311275 := by
  unfold tailWord_3094880
  simp only [CollatzResearch.WordTrace]
  refine ⟨56439773513892899134013047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75253031351857198845350729 56439773513892899134013047)
  ·
    refine ⟨84659660270839348701019571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56439773513892899134013047 84659660270839348701019571)
    ·
      refine ⟨126989490406259023051529357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84659660270839348701019571 126989490406259023051529357)
      ·
        refine ⟨47621058902347133644323509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126989490406259023051529357 47621058902347133644323509)
        ·
          refine ⟨4464474272095043779155329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47621058902347133644323509 4464474272095043779155329)
          ·
            refine ⟨3348355704071282834366497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4464474272095043779155329 3348355704071282834366497)
            ·
              refine ⟨2511266778053462125774873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3348355704071282834366497 2511266778053462125774873)
              ·
                refine ⟨1883450083540096594331155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2511266778053462125774873 1883450083540096594331155)
                ·
                  refine ⟨2825175125310144891496733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883450083540096594331155 2825175125310144891496733)
                  ·
                    refine ⟨1059440671991304334311275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825175125310144891496733 1059440671991304334311275)
                    ·
                      rfl

theorem cell22_3094880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_3094880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094880 prefixEnd_3094880 := by exact prefixLift 3094880
  have htrace : WordTrace (prefixWord ++ tailWord_3094880) baseStart_3094880 baseEnd_3094880 := by
    simpa [prefixWord, tailWord_3094880, baseEnd_3094880] using wordTrace_append hprefix tailTrace_3094880
  have hstable : (prefixWord ++ tailWord_3094880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094880).length < 2 ^ (prefixWord ++ tailWord_3094880).sum := by decide
  have hdescent : baseEnd_3094880 < baseStart_3094880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094919 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 4, 3]
def baseStart_3094919 : Nat := 118140960795 + 3094919 * 2 ^ 59
def prefixEnd_3094919 : Nat := 4983230072969 + 3 ^ 40 * 3094919 * 2
def baseEnd_3094919 : Nat := 1059454022488321232586155

theorem tailTrace_3094919 : CollatzResearch.WordTrace tailWord_3094919 prefixEnd_3094919 1059454022488321232586155 := by
  unfold tailWord_3094919
  simp only [CollatzResearch.WordTrace]
  refine ⟨112880969474644507928695811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75253979649763005285797207 112880969474644507928695811)
  ·
    refine ⟨169321454211966761893043717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112880969474644507928695811 169321454211966761893043717)
    ·
      refine ⟨31747772664743767854945697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169321454211966761893043717 31747772664743767854945697)
      ·
        refine ⟨23810829498557825891209273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31747772664743767854945697 23810829498557825891209273)
        ·
          refine ⟨17858122123918369418406955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23810829498557825891209273 17858122123918369418406955)
          ·
            refine ⟨26787183185877554127610433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17858122123918369418406955 26787183185877554127610433)
            ·
              refine ⟨20090387389408165595707825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26787183185877554127610433 20090387389408165595707825)
              ·
                refine ⟨15067790542056124196780869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20090387389408165595707825 15067790542056124196780869)
                ·
                  refine ⟨2825210726635523286896413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15067790542056124196780869 2825210726635523286896413)
                  ·
                    refine ⟨1059454022488321232586155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825210726635523286896413 1059454022488321232586155)
                    ·
                      rfl

theorem cell22_3094919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_3094919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094919 prefixEnd_3094919 := by exact prefixLift 3094919
  have htrace : WordTrace (prefixWord ++ tailWord_3094919) baseStart_3094919 baseEnd_3094919 := by
    simpa [prefixWord, tailWord_3094919, baseEnd_3094919] using wordTrace_append hprefix tailTrace_3094919
  have hstable : (prefixWord ++ tailWord_3094919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094919).length < 2 ^ (prefixWord ++ tailWord_3094919).sum := by decide
  have hdescent : baseEnd_3094919 < baseStart_3094919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094921 : List Nat := [1, 2, 1, 1, 6, 2, 2, 3, 4]
def baseStart_3094921 : Nat := 118140960795 + 3094921 * 2 ^ 59
def prefixEnd_3094921 : Nat := 4983230072969 + 3 ^ 40 * 3094921 * 2
def baseEnd_3094921 : Nat := 353151569043064631345383

theorem tailTrace_3094921 : CollatzResearch.WordTrace tailWord_3094921 prefixEnd_3094921 353151569043064631345383 := by
  unfold tailWord_3094921
  simp only [CollatzResearch.WordTrace]
  refine ⟨112881042420637262270268617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75254028280424841513512411 112881042420637262270268617)
  ·
    refine ⟨84660781815477946702701463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112881042420637262270268617 84660781815477946702701463)
    ·
      refine ⟨126991172723216920054052195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84660781815477946702701463 126991172723216920054052195)
      ·
        refine ⟨190486759084825380081078293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126991172723216920054052195 190486759084825380081078293)
        ·
          refine ⟨8929066832101189691300545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190486759084825380081078293 8929066832101189691300545)
          ·
            refine ⟨6696800124075892268475409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8929066832101189691300545 6696800124075892268475409)
            ·
              refine ⟨5022600093056919201356557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6696800124075892268475409 5022600093056919201356557)
              ·
                refine ⟨1883475034896344700508709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5022600093056919201356557 1883475034896344700508709)
                ·
                  refine ⟨353151569043064631345383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1883475034896344700508709 353151569043064631345383)
                  ·
                    rfl

theorem cell22_3094921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 3, 4].length) (baseStart_3094921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094921 prefixEnd_3094921 := by exact prefixLift 3094921
  have htrace : WordTrace (prefixWord ++ tailWord_3094921) baseStart_3094921 baseEnd_3094921 := by
    simpa [prefixWord, tailWord_3094921, baseEnd_3094921] using wordTrace_append hprefix tailTrace_3094921
  have hstable : (prefixWord ++ tailWord_3094921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094921).length < 2 ^ (prefixWord ++ tailWord_3094921).sum := by decide
  have hdescent : baseEnd_3094921 < baseStart_3094921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3094936 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_3094936 : Nat := 118140960795 + 3094936 * 2 ^ 59
def prefixEnd_3094936 : Nat := 4983230072969 + 3 ^ 40 * 3094936 * 2
def baseEnd_3094936 : Nat := 1059459841935738854911103

theorem tailTrace_3094936 : CollatzResearch.WordTrace tailWord_3094936 prefixEnd_3094936 1059459841935738854911103 := by
  unfold tailWord_3094936
  simp only [CollatzResearch.WordTrace]
  refine ⟨56440794757791459916032331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75254393010388613221376441 56440794757791459916032331)
  ·
    refine ⟨84661192136687189874048497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56440794757791459916032331 84661192136687189874048497)
    ·
      refine ⟨63495894102515392405536373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84661192136687189874048497 63495894102515392405536373)
      ·
        refine ⟨5952740072110818038019035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63495894102515392405536373 5952740072110818038019035)
        ·
          refine ⟨8929110108166227057028553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5952740072110818038019035 8929110108166227057028553)
          ·
            refine ⟨6696832581124670292771415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8929110108166227057028553 6696832581124670292771415)
            ·
              refine ⟨10045248871687005439157123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696832581124670292771415 10045248871687005439157123)
              ·
                refine ⟨15067873307530508158735685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045248871687005439157123 15067873307530508158735685)
                ·
                  refine ⟨2825226245161970279762941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15067873307530508158735685 2825226245161970279762941)
                  ·
                    refine ⟨1059459841935738854911103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825226245161970279762941 1059459841935738854911103)
                    ·
                      rfl

theorem cell22_3094936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_3094936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3094936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3094936 prefixEnd_3094936 := by exact prefixLift 3094936
  have htrace : WordTrace (prefixWord ++ tailWord_3094936) baseStart_3094936 baseEnd_3094936 := by
    simpa [prefixWord, tailWord_3094936, baseEnd_3094936] using wordTrace_append hprefix tailTrace_3094936
  have hstable : (prefixWord ++ tailWord_3094936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3094936).length < 2 ^ (prefixWord ++ tailWord_3094936).sum := by decide
  have hdescent : baseEnd_3094936 < baseStart_3094936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3094936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095011 : List Nat := [1, 1, 1, 6, 3, 1, 1, 3, 5]
def baseStart_3095011 : Nat := 118140960795 + 3095011 * 2 ^ 59
def prefixEnd_3095011 : Nat := 4983230072969 + 3 ^ 40 * 3095011 * 2
def baseEnd_3095011 : Nat := 353161838656154553095291

theorem tailTrace_3095011 : CollatzResearch.WordTrace tailWord_3095011 prefixEnd_3095011 353161838656154553095291 := by
  unfold tailWord_3095011
  simp only [CollatzResearch.WordTrace]
  refine ⟨112884324990311207641044887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75256216660207471760696591 112884324990311207641044887)
  ·
    refine ⟨169326487485466811461567331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112884324990311207641044887 169326487485466811461567331)
    ·
      refine ⟨253989731228200217192350997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169326487485466811461567331 253989731228200217192350997)
      ·
        refine ⟨11905768651321885180891453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 253989731228200217192350997 11905768651321885180891453)
        ·
          refine ⟨4464663244245706942834295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11905768651321885180891453 4464663244245706942834295)
          ·
            refine ⟨6696994866368560414251443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4464663244245706942834295 6696994866368560414251443)
            ·
              refine ⟨10045492299552840621377165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6696994866368560414251443 10045492299552840621377165)
              ·
                refine ⟨3767059612332315233016437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10045492299552840621377165 3767059612332315233016437)
                ·
                  refine ⟨353161838656154553095291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3767059612332315233016437 353161838656154553095291)
                  ·
                    rfl

theorem cell22_3095011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 3, 5].length) (baseStart_3095011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095011 prefixEnd_3095011 := by exact prefixLift 3095011
  have htrace : WordTrace (prefixWord ++ tailWord_3095011) baseStart_3095011 baseEnd_3095011 := by
    simpa [prefixWord, tailWord_3095011, baseEnd_3095011] using wordTrace_append hprefix tailTrace_3095011
  have hstable : (prefixWord ++ tailWord_3095011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095011).length < 2 ^ (prefixWord ++ tailWord_3095011).sum := by decide
  have hdescent : baseEnd_3095011 < baseStart_3095011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095024 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_3095024 : Nat := 118140960795 + 3095024 * 2 ^ 59
def prefixEnd_3095024 : Nat := 4983230072969 + 3 ^ 40 * 3095024 * 2
def baseEnd_3095024 : Nat := 1059489966134135958710833

theorem tailTrace_3095024 : CollatzResearch.WordTrace tailWord_3095024 prefixEnd_3095024 1059489966134135958710833 := by
  unfold tailWord_3095024
  simp only [CollatzResearch.WordTrace]
  refine ⟨56442399569632055430634063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75256532759509407240845417 56442399569632055430634063)
  ·
    refine ⟨84663599354448083145951095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56442399569632055430634063 84663599354448083145951095)
    ·
      refine ⟨126995399031672124718926643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84663599354448083145951095 126995399031672124718926643)
      ·
        refine ⟨190493098547508187078389965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126995399031672124718926643 190493098547508187078389965)
        ·
          refine ⟨71434911955315570154396237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190493098547508187078389965 71434911955315570154396237)
          ·
            refine ⟨26788091983243338807898589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71434911955315570154396237 26788091983243338807898589)
            ·
              refine ⟨10045534493716252052961971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26788091983243338807898589 10045534493716252052961971)
              ·
                refine ⟨15068301740574378079442957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10045534493716252052961971 15068301740574378079442957)
                ·
                  refine ⟨5650613152715391779791109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15068301740574378079442957 5650613152715391779791109)
                  ·
                    refine ⟨1059489966134135958710833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5650613152715391779791109 1059489966134135958710833)
                    ·
                      rfl

theorem cell22_3095024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_3095024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095024 prefixEnd_3095024 := by exact prefixLift 3095024
  have htrace : WordTrace (prefixWord ++ tailWord_3095024) baseStart_3095024 baseEnd_3095024 := by
    simpa [prefixWord, tailWord_3095024, baseEnd_3095024] using wordTrace_append hprefix tailTrace_3095024
  have hstable : (prefixWord ++ tailWord_3095024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095024).length < 2 ^ (prefixWord ++ tailWord_3095024).sum := by decide
  have hdescent : baseEnd_3095024 < baseStart_3095024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095105 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3095105 : Nat := 118140960795 + 3095105 * 2 ^ 59
def prefixEnd_3095105 : Nat := 4983230072969 + 3 ^ 40 * 3095105 * 2
def baseEnd_3095105 : Nat := 1059517694089478747435585

theorem tailTrace_3095105 : CollatzResearch.WordTrace tailWord_3095105 prefixEnd_3095105 1059517694089478747435585 := by
  unfold tailWord_3095105
  simp only [CollatzResearch.WordTrace]
  refine ⟨112887753451970661694966769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75258502301313774463311179 112887753451970661694966769)
  ·
    refine ⟨84665815088977996271225077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112887753451970661694966769 84665815088977996271225077)
    ·
      refine ⟨7937420164591687150427351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84665815088977996271225077 7937420164591687150427351)
      ·
        refine ⟨11906130246887530725641027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7937420164591687150427351 11906130246887530725641027)
        ·
          refine ⟨17859195370331296088461541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11906130246887530725641027 17859195370331296088461541)
          ·
            refine ⟨3348599131937118016586539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17859195370331296088461541 3348599131937118016586539)
            ·
              refine ⟨5022898697905677024879809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348599131937118016586539 5022898697905677024879809)
              ·
                refine ⟨3767174023429257768659857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5022898697905677024879809 3767174023429257768659857)
                ·
                  refine ⟨2825380517571943326494893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3767174023429257768659857 2825380517571943326494893)
                  ·
                    refine ⟨1059517694089478747435585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825380517571943326494893 1059517694089478747435585)
                    ·
                      rfl

theorem cell22_3095105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3095105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095105 prefixEnd_3095105 := by exact prefixLift 3095105
  have htrace : WordTrace (prefixWord ++ tailWord_3095105) baseStart_3095105 baseEnd_3095105 := by
    simpa [prefixWord, tailWord_3095105, baseEnd_3095105] using wordTrace_append hprefix tailTrace_3095105
  have hstable : (prefixWord ++ tailWord_3095105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095105).length < 2 ^ (prefixWord ++ tailWord_3095105).sum := by decide
  have hdescent : baseEnd_3095105 < baseStart_3095105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095219 : List Nat := [1, 1, 1, 2, 3, 14]
def baseStart_3095219 : Nat := 118140960795 + 3095219 * 2 ^ 59
def prefixEnd_3095219 : Nat := 4983230072969 + 3 ^ 40 * 3095219 * 2
def baseEnd_3095219 : Nat := 13080947143447166050435

theorem tailTrace_3095219 : CollatzResearch.WordTrace tailWord_3095219 prefixEnd_3095219 13080947143447166050435 := by
  unfold tailWord_3095219
  simp only [CollatzResearch.WordTrace]
  refine ⟨112891911373557659164616711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75261274249038439443077807 112891911373557659164616711)
  ·
    refine ⟨169337867060336488746925067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112891911373557659164616711 169337867060336488746925067)
    ·
      refine ⟨254006800590504733120387601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169337867060336488746925067 254006800590504733120387601)
      ·
        refine ⟨190505100442878549840290701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254006800590504733120387601 190505100442878549840290701)
        ·
          refine ⟨71439412666079456190109013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190505100442878549840290701 71439412666079456190109013)
          ·
            refine ⟨13080947143447166050435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 71439412666079456190109013 13080947143447166050435)
            ·
              rfl

theorem cell22_3095219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 14].length) (baseStart_3095219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095219 prefixEnd_3095219 := by exact prefixLift 3095219
  have htrace : WordTrace (prefixWord ++ tailWord_3095219) baseStart_3095219 baseEnd_3095219 := by
    simpa [prefixWord, tailWord_3095219, baseEnd_3095219] using wordTrace_append hprefix tailTrace_3095219
  have hstable : (prefixWord ++ tailWord_3095219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095219).length < 2 ^ (prefixWord ++ tailWord_3095219).sum := by decide
  have hdescent : baseEnd_3095219 < baseStart_3095219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095281 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 7]
def baseStart_3095281 : Nat := 118140960795 + 3095281 * 2 ^ 59
def prefixEnd_3095281 : Nat := 4983230072969 + 3 ^ 40 * 3095281 * 2
def baseEnd_3095281 : Nat := 353192647495424318345015

theorem tailTrace_3095281 : CollatzResearch.WordTrace tailWord_3095281 prefixEnd_3095281 353192647495424318345015 := by
  unfold tailWord_3095281
  simp only [CollatzResearch.WordTrace]
  refine ⟨112894172699333043753373697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75262781799555362502249131 112894172699333043753373697)
  ·
    refine ⟨84670629524499782815030273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112894172699333043753373697 84670629524499782815030273)
    ·
      refine ⟨63502972143374837111272705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84670629524499782815030273 63502972143374837111272705)
      ·
        refine ⟨47627229107531127833454529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63502972143374837111272705 47627229107531127833454529)
        ·
          refine ⟨35720421830648345875090897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47627229107531127833454529 35720421830648345875090897)
          ·
            refine ⟨26790316372986259406318173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35720421830648345875090897 26790316372986259406318173)
            ·
              refine ⟨10046368639869847277369315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26790316372986259406318173 10046368639869847277369315)
              ·
                refine ⟨15069552959804770916053973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046368639869847277369315 15069552959804770916053973)
                ·
                  refine ⟨353192647495424318345015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15069552959804770916053973 353192647495424318345015)
                  ·
                    rfl

theorem cell22_3095281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 7].length) (baseStart_3095281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095281 prefixEnd_3095281 := by exact prefixLift 3095281
  have htrace : WordTrace (prefixWord ++ tailWord_3095281) baseStart_3095281 baseEnd_3095281 := by
    simpa [prefixWord, tailWord_3095281, baseEnd_3095281] using wordTrace_append hprefix tailTrace_3095281
  have hstable : (prefixWord ++ tailWord_3095281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095281).length < 2 ^ (prefixWord ++ tailWord_3095281).sum := by decide
  have hdescent : baseEnd_3095281 < baseStart_3095281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095319 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 1, 3]
def baseStart_3095319 : Nat := 118140960795 + 3095319 * 2 ^ 59
def prefixEnd_3095319 : Nat := 4983230072969 + 3 ^ 40 * 3095319 * 2
def baseEnd_3095319 : Nat := 1059590950662853522584929

theorem tailTrace_3095319 : CollatzResearch.WordTrace tailWord_3095319 prefixEnd_3095319 1059590950662853522584929 := by
  unfold tailWord_3095319
  simp only [CollatzResearch.WordTrace]
  refine ⟨112895558673195376243257011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 75263705782130250828838007 112895558673195376243257011)
  ·
    refine ⟨169343338009793064364885517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112895558673195376243257011 169343338009793064364885517)
    ·
      refine ⟨63503751753672399136832069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169343338009793064364885517 63503751753672399136832069)
      ·
        refine ⟨11906953453813574838156013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63503751753672399136832069 11906953453813574838156013)
        ·
          refine ⟨4465107545180090564308505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11906953453813574838156013 4465107545180090564308505)
          ·
            refine ⟨3348830658885067923231379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4465107545180090564308505 3348830658885067923231379)
            ·
              refine ⟨5023245988327601884847069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3348830658885067923231379 5023245988327601884847069)
              ·
                refine ⟨1883717245622850706817651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5023245988327601884847069 1883717245622850706817651)
                ·
                  refine ⟨2825575868434276060226477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883717245622850706817651 2825575868434276060226477)
                  ·
                    refine ⟨1059590950662853522584929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2825575868434276060226477 1059590950662853522584929)
                    ·
                      rfl

theorem cell22_3095319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_3095319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095319 prefixEnd_3095319 := by exact prefixLift 3095319
  have htrace : WordTrace (prefixWord ++ tailWord_3095319) baseStart_3095319 baseEnd_3095319 := by
    simpa [prefixWord, tailWord_3095319, baseEnd_3095319] using wordTrace_append hprefix tailTrace_3095319
  have hstable : (prefixWord ++ tailWord_3095319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095319).length < 2 ^ (prefixWord ++ tailWord_3095319).sum := by decide
  have hdescent : baseEnd_3095319 < baseStart_3095319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095388 : List Nat := [2, 2, 4, 2, 1, 11]
def baseStart_3095388 : Nat := 118140960795 + 3095388 * 2 ^ 59
def prefixEnd_3095388 : Nat := 4983230072969 + 3 ^ 40 * 3095388 * 2
def baseEnd_3095388 : Nat := 13081661367567411637157

theorem tailTrace_3095388 : CollatzResearch.WordTrace tailWord_3095388 prefixEnd_3095388 13081661367567411637157 := by
  unfold tailWord_3095388
  simp only [CollatzResearch.WordTrace]
  refine ⟨56449037654972700513759409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75265383539963600685012545 56449037654972700513759409)
  ·
    refine ⟨42336778241229525385319557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56449037654972700513759409 42336778241229525385319557)
    ·
      refine ⟨7938145920230536009747417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42336778241229525385319557 7938145920230536009747417)
      ·
        refine ⟨5953609440172902007310563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7938145920230536009747417 5953609440172902007310563)
        ·
          refine ⟨8930414160259353010965845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5953609440172902007310563 8930414160259353010965845)
          ·
            refine ⟨13081661367567411637157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8930414160259353010965845 13081661367567411637157)
            ·
              rfl

theorem cell22_3095388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 11].length) (baseStart_3095388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095388 prefixEnd_3095388 := by exact prefixLift 3095388
  have htrace : WordTrace (prefixWord ++ tailWord_3095388) baseStart_3095388 baseEnd_3095388 := by
    simpa [prefixWord, tailWord_3095388, baseEnd_3095388] using wordTrace_append hprefix tailTrace_3095388
  have hstable : (prefixWord ++ tailWord_3095388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095388).length < 2 ^ (prefixWord ++ tailWord_3095388).sum := by decide
  have hdescent : baseEnd_3095388 < baseStart_3095388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095450 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_3095450 : Nat := 118140960795 + 3095450 * 2 ^ 59
def prefixEnd_3095450 : Nat := 4983230072969 + 3 ^ 40 * 3095450 * 2
def baseEnd_3095450 : Nat := 353211931546670949186509

theorem tailTrace_3095450 : CollatzResearch.WordTrace tailWord_3095450 prefixEnd_3095450 353211931546670949186509 := by
  unfold tailWord_3095450
  simp only [CollatzResearch.WordTrace]
  refine ⟨28225084158930196404068951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 75266891090480523744183869 28225084158930196404068951)
  ·
    refine ⟨42337626238395294606103427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28225084158930196404068951 42337626238395294606103427)
    ·
      refine ⟨63506439357592941909155141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42337626238395294606103427 63506439357592941909155141)
      ·
        refine ⟨11907457379548676607966589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63506439357592941909155141 11907457379548676607966589)
        ·
          refine ⟨4465296517330753727987471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11907457379548676607966589 4465296517330753727987471)
          ·
            refine ⟨6697944775996130591981207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4465296517330753727987471 6697944775996130591981207)
            ·
              refine ⟨10046917163994195887971811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6697944775996130591981207 10046917163994195887971811)
              ·
                refine ⟨15070375745991293831957717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10046917163994195887971811 15070375745991293831957717)
                ·
                  refine ⟨353211931546670949186509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15070375745991293831957717 353211931546670949186509)
                  ·
                    rfl

theorem cell22_3095450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_3095450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095450 prefixEnd_3095450 := by exact prefixLift 3095450
  have htrace : WordTrace (prefixWord ++ tailWord_3095450) baseStart_3095450 baseEnd_3095450 := by
    simpa [prefixWord, tailWord_3095450, baseEnd_3095450] using wordTrace_append hprefix tailTrace_3095450
  have hstable : (prefixWord ++ tailWord_3095450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095450).length < 2 ^ (prefixWord ++ tailWord_3095450).sum := by decide
  have hdescent : baseEnd_3095450 < baseStart_3095450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095480 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_3095480 : Nat := 118140960795 + 3095480 * 2 ^ 59
def prefixEnd_3095480 : Nat := 4983230072969 + 3 ^ 40 * 3095480 * 2
def baseEnd_3095480 : Nat := 1059646064253102769309435

theorem tailTrace_3095480 : CollatzResearch.WordTrace tailWord_3095480 prefixEnd_3095480 1059646064253102769309435 := by
  unfold tailWord_3095480
  simp only [CollatzResearch.WordTrace]
  refine ⟨56450715412806050369933947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 75267620550408067159911929 56450715412806050369933947)
  ·
    refine ⟨84676073119209075554900921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56450715412806050369933947 84676073119209075554900921)
    ·
      refine ⟨63507054839406806666175691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84676073119209075554900921 63507054839406806666175691)
      ·
        refine ⟨95260582259110209999263537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63507054839406806666175691 95260582259110209999263537)
        ·
          refine ⟨71445436694332657499447653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95260582259110209999263537 71445436694332657499447653)
          ·
            refine ⟨13396019380187373281146435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71445436694332657499447653 13396019380187373281146435)
            ·
              refine ⟨20094029070281059921719653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13396019380187373281146435 20094029070281059921719653)
              ·
                refine ⟨3767630450677698735322435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20094029070281059921719653 3767630450677698735322435)
                ·
                  refine ⟨5651445676016548102983653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3767630450677698735322435 5651445676016548102983653)
                  ·
                    refine ⟨1059646064253102769309435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651445676016548102983653 1059646064253102769309435)
                    ·
                      rfl

theorem cell22_3095480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_3095480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095480 prefixEnd_3095480 := by exact prefixLift 3095480
  have htrace : WordTrace (prefixWord ++ tailWord_3095480) baseStart_3095480 baseEnd_3095480 := by
    simpa [prefixWord, tailWord_3095480, baseEnd_3095480] using wordTrace_append hprefix tailTrace_3095480
  have hstable : (prefixWord ++ tailWord_3095480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095480).length < 2 ^ (prefixWord ++ tailWord_3095480).sum := by decide
  have hdescent : baseEnd_3095480 < baseStart_3095480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3095542 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3095542 : Nat := 118140960795 + 3095542 * 2 ^ 59
def prefixEnd_3095542 : Nat := 4983230072969 + 3 ^ 40 * 3095542 * 2
def baseEnd_3095542 : Nat := 1059667288120155274259245

theorem tailTrace_3095542 : CollatzResearch.WordTrace tailWord_3095542 prefixEnd_3095542 1059667288120155274259245 := by
  unfold tailWord_3095542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056480759461717833039055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 75269128100924990219083253 7056480759461717833039055)
  ·
    refine ⟨10584721139192576749558583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7056480759461717833039055 10584721139192576749558583)
    ·
      refine ⟨15877081708788865124337875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10584721139192576749558583 15877081708788865124337875)
      ·
        refine ⟨23815622563183297686506813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15877081708788865124337875 23815622563183297686506813)
        ·
          refine ⟨8930858461193736632440055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23815622563183297686506813 8930858461193736632440055)
          ·
            refine ⟨13396287691790604948660083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8930858461193736632440055 13396287691790604948660083)
            ·
              refine ⟨20094431537685907422990125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13396287691790604948660083 20094431537685907422990125)
              ·
                refine ⟨7535411826632215283621297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20094431537685907422990125 7535411826632215283621297)
                ·
                  refine ⟨5651558869974161462715973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7535411826632215283621297 5651558869974161462715973)
                  ·
                    refine ⟨1059667288120155274259245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5651558869974161462715973 1059667288120155274259245)
                    ·
                      rfl

theorem cell22_3095542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3095542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3095542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3095542 prefixEnd_3095542 := by exact prefixLift 3095542
  have htrace : WordTrace (prefixWord ++ tailWord_3095542) baseStart_3095542 baseEnd_3095542 := by
    simpa [prefixWord, tailWord_3095542, baseEnd_3095542] using wordTrace_append hprefix tailTrace_3095542
  have hstable : (prefixWord ++ tailWord_3095542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3095542).length < 2 ^ (prefixWord ++ tailWord_3095542).sum := by decide
  have hdescent : baseEnd_3095542 < baseStart_3095542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3095542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
